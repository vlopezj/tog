{-# LANGUAGE OverloadedStrings #-}
module TypeCheck3.Solve.Simple
  ( SolveState
  , initSolveState
  , prettySolveState
  , solve
  ) where

import           Prelude                          hiding (any)

import           Control.Monad.State.Strict       (get, put)
import           Control.Monad.Trans.Maybe        (runMaybeT)
import           Control.Monad.Trans.Writer.Strict (WriterT, execWriterT, tell)
import qualified Data.HashSet                     as HS
import qualified Data.Set                         as Set
import           Syntax.Internal                  (Name)

import           Prelude.Extended
import           PrettyPrint                      (($$), (<+>), (//>), (//), group, hang)
import qualified PrettyPrint                      as PP
import           Term
import           Term.Context                     (Ctx)
import qualified Term.Context                     as Ctx
import qualified Term.Signature                   as Sig
import qualified Term.Telescope                   as Tel
import qualified TypeCheck3.Common                as Common
import           TypeCheck3.Common                hiding (Constraint(..), prettyConstraintTC)
import           TypeCheck3.Monad
import           TypeCheck3.Solve.Common

-- These definitions should be in every Solve module
----------------------------------------------------

newtype SolveState t = SolveState (Constraints t)

type BlockingMetas = HS.HashSet MetaVar
type Constraints t = [(BlockingMetas, Constraint t)]

data Constraint t
  = Unify (Ctx t) (Type t) (Term t) (Term t)
  | UnifySpine (Ctx t) (Type t) (Maybe (Term t)) [Elim (Term t)] [Elim (Term t)]
  | Conj [Constraint t]
  | (:>>:) (Constraint t) (Constraint t)

simplify :: Constraint t -> Maybe (Constraint t)
simplify (Conj [])    = Nothing
simplify (Conj [c])   = simplify c
simplify (Conj cs)    = msum $ map simplify $ concatMap flatten cs
  where
    flatten (Conj constrs) = concatMap flatten constrs
    flatten c              = [c]
simplify (c1 :>>: c2) = case simplify c1 of
                          Nothing  -> simplify c2
                          Just c1' -> Just (c1' :>>: c2)
simplify c            = Just c

instance Monoid (Constraint t) where
  mempty = Conj []

  Conj cs1 `mappend` Conj cs2 = Conj (cs1 ++ cs2)
  Conj cs1 `mappend` c2       = Conj (c2 : cs1)
  c1       `mappend` Conj cs2 = Conj (c1 : cs2)
  c1       `mappend` c2       = Conj [c1, c2]

constraint :: Common.Constraint t -> Constraint t
constraint (Common.Unify ctx type_ t1 t2) = Unify ctx type_ t1 t2
constraint (Common.Conj cs) = Conj $ map constraint cs
constraint (c1 Common.:>>: c2) = constraint c1 :>>: constraint c2

initSolveState :: SolveState t
initSolveState = SolveState []

solve :: forall t. (IsTerm t) => Common.Constraint t -> TC t (SolveState t) ()
solve c = do
  debugBracket_ "*** solve" $ do
    SolveState constrs0 <- get
    constrs <- go False [] ((mempty, constraint c) : constrs0)
    put $ SolveState constrs
  where
    go :: Bool -> Constraints t -> Constraints t -> TC t s (Constraints t)
    go progress constrs [] = do
      if progress
      then go False [] constrs
      else return constrs
    go progress newConstrs ((mvs, constr) : constrs) = do
      debug $ do
        let mvsDoc = PP.pretty $ HS.toList mvs
        constrDoc <- prettyConstraintTC constr
        return $
          "** Attempting" $$
          "constraint:" //> constrDoc $$
          "mvs:" //> mvsDoc
      attempt <- do mvsBodies <- forM (HS.toList mvs) getMetaVarBody
                    return $ null mvsBodies || any isJust mvsBodies
      if attempt
        then do
          constrs' <- solve' constr
          go True (constrs' ++ newConstrs) constrs
        else do
          go progress ((mvs, constr) : newConstrs) constrs

solve' :: (IsTerm t) => Constraint t -> TC t s (Constraints t)
solve' (Conj constrs) = do
  mconcat <$> forM constrs solve'
solve' (constr1 :>>: constr2) = do
  constrs1_0 <- solve' constr1
  let mbConstrs1 = mconcat [ fmap (\c -> [(mvs, c)]) (simplify constr)
                           | (mvs, constr) <- constrs1_0 ]
  case mbConstrs1 of
    Nothing -> do
      solve' constr2
    Just constrs1 -> do
      let (mvs, constr1') = mconcat constrs1
      return [(mvs, constr1' :>>: constr2)]
solve' (Unify ctx type_ t1 t2) = do
  checkEqual (ctx, type_, t1, t2)
solve' (UnifySpine ctx type_ mbH elims1 elims2) = do
  checkEqualSpine' ctx type_ mbH elims1 elims2

prettySolveState
  :: (IsTerm t) => Sig.Signature t -> Bool -> SolveState t -> TermM PP.Doc
prettySolveState sig detailed (SolveState cs) = execWriterT $ go cs
  where
    go cs = do
      tell $ "-- Unsolved problems:" <+> PP.pretty (length cs)
      when detailed $ forM_ cs $ \(mvs, c) -> do
        tell $ PP.line <> "------------------------------------------------------------------------"
        cDoc <- lift $ prettyConstraint sig c
        tell $ PP.line <> "** Waiting on" <+> PP.pretty (HS.toList mvs) $$ cDoc

-- This is local stuff
----------------------

sequenceConstraints :: Constraints t -> Constraint t -> Constraints t
sequenceConstraints scs1 c2 =
  let (css, cs1) = unzip scs1 in [(mconcat css, Conj cs1 :>>: c2)]

-- Equality
------------------------------------------------------------------------

type CheckEqual t = (Ctx t, Type t, Term t, Term t)

checkEqual
  :: (IsTerm t) => CheckEqual t -> TC t s (Constraints t)
checkEqual (ctx0, type0, t1_0, t2_0) = do
  let msg = do
        ctxDoc <- prettyContextTC ctx0
        typeDoc <- prettyTermTC type0
        xDoc <- prettyTermTC t1_0
        yDoc <- prettyTermTC t2_0
        return $
          "*** checkEqual" $$
          "ctx:" //> ctxDoc $$
          "type:" //> typeDoc $$
          "x:" //> xDoc $$
          "y:" //> yDoc
  debugBracket msg $ do
    runCheckEqual
      [checkSynEq, etaExpand, checkMetaVars]
      compareTerms
      (ctx0, type0, t1_0, t2_0)
  where
    runCheckEqual actions0 finally args = do
      case actions0 of
        []                 -> finally args
        (action : actions) -> do
          constrsOrArgs <- action args
          case constrsOrArgs of
            Left constrs -> return constrs
            Right args'  -> runCheckEqual actions finally args'

checkSynEq
  :: (IsTerm t)
  => CheckEqual t -> TC t s (Either (Constraints t) (CheckEqual t))
checkSynEq (ctx, type_, t1, t2) = do
  debugBracket_ "*** Syntactic check" $ do
    -- Optimization: try with a simple syntactic check first.
    t1' <- ignoreBlockingTC =<< whnfTC t1
    t2' <- ignoreBlockingTC =<< whnfTC t2
    -- TODO add option to skip this check
    eq <- termEqTC t1' t2'
    return $ if eq
      then Left []
      else Right (ctx, type_, t1', t2')

etaExpand
  :: (IsTerm t)
  => CheckEqual t -> TC t s (Either (Constraints t) (CheckEqual t))
etaExpand (ctx, type0, t1, t2) = do
  debugBracket_ "*** Eta expansion" $ do
    -- TODO compute expanding function once
    t1' <- expandOrDont "x" type0 t1
    t2' <- expandOrDont "y" type0 t2
    return $ Right (ctx, type0, t1', t2')
  where
    expandOrDont desc type_ t = do
      mbT <- expand type_ t
      case mbT of
        Nothing -> do
          debug_ $ "** Couldn't expand" <+> desc
          return t
        Just t' -> do
          debug $ do
            tDoc <- prettyTermTC t'
            return $
              "** Expanded" <+> desc <+> "to" //> tDoc
          return t'

    expand type_ t = do
      typeView <- whnfViewTC type_
      case typeView of
        App (Def tyCon) _ -> do
          tyConDef <- getDefinition tyCon
          case tyConDef of
            Constant (Record dataCon projs) _ -> do
              tView <- whnfViewTC t
              case tView of
                Con _ _ -> return Nothing
                _       -> do
                  ts <- mapM (\(n, ix) -> eliminateTC t [Proj n ix]) projs
                  Just <$> conTC dataCon ts
            _ ->
              return Nothing
        Pi _ codomain -> do
          name <- getAbsNameTC codomain
          v <- varTC $ boundVar name
          tView <- whnfViewTC t
          case tView of
            Lam _ -> return Nothing
            _     -> do t' <- liftTermM $ weaken_ 1 t
                        t'' <- lamTC =<< eliminateTC t' [Apply v]
                        return $ Just t''
        _ ->
          return Nothing

checkMetaVars
  :: (IsTerm t)
  => CheckEqual t -> TC t s (Either (Constraints t) (CheckEqual t))
checkMetaVars (ctx, type_, t1, t2) = do
  blockedT1 <- whnfTC t1
  t1' <- ignoreBlockingTC blockedT1
  blockedT2 <- whnfTC t2
  t2' <- ignoreBlockingTC blockedT2
  let syntacticEqualityOrPostpone mvs = do
        t1'' <- nfTC t1'
        t2'' <- nfTC t2'
        eq <- liftTermM $ termEq t1'' t2''
        if eq
          then return $ Left []
          else do
            debug_ $ "*** Both sides blocked, waiting for" <+> PP.pretty (HS.toList mvs)
            return $ Left [(mvs, Unify ctx type_ t1'' t2'')]
  case (blockedT1, blockedT2) of
    (MetaVarHead mv els1, MetaVarHead mv' els2) | mv == mv' -> do
      mbKills <- intersectVars els1 els2
      case mbKills of
        Nothing -> do
          syntacticEqualityOrPostpone $ HS.singleton mv
        Just kills -> do
          instantiateMetaVar mv =<< killArgs mv kills
          return (Left [])
    (MetaVarHead mv elims, _) -> do
      Left <$> metaAssign ctx type_ mv elims t2
    (_, MetaVarHead mv elims) -> do
      Left <$> metaAssign ctx type_ mv elims t1
    (BlockedOn mvs1 _ _, BlockedOn mvs2 _ _) -> do
      -- Both blocked, and we already checked for syntactic equality,
      -- let's try syntactic equality when normalized.
      syntacticEqualityOrPostpone (mvs1 <> mvs2)
    (BlockedOn mvs f elims, _) -> do
      Left <$> checkEqualBlockedOn ctx type_ mvs f elims t2
    (_, BlockedOn mvs f elims) -> do
      Left <$> checkEqualBlockedOn ctx type_ mvs f elims t1
    (NotBlocked _, NotBlocked _) -> do
      return $ Right (ctx, type_, t1', t2')

checkEqualBlockedOn
  :: forall t s.
     (IsTerm t)
  => Ctx t -> Type t
  -> HS.HashSet MetaVar -> BlockedHead -> [Elim t]
  -> Term t
  -> TC t s (Constraints t)
checkEqualBlockedOn ctx type_ mvs bh elims1 t2 = do
  let msg = "*** Equality blocked on metavars" <+> PP.pretty (HS.toList mvs) PP.<>
            ", trying to invert definition" <+> PP.pretty bh
  t1 <- ignoreBlockingTC $ BlockedOn mvs bh elims1
  debugBracket_ msg $ do
    case bh of
      BlockedOnJ -> do
        debug_ "** Head is J, couldn't invert."
        fallback t1
      BlockedOnFunction fun1 -> do
        Function _ clauses <- getDefinition fun1
        case clauses of
          NotInvertible _ -> do
            debug_ "** Couldn't invert."
            fallback t1
          Invertible injClauses -> do
            t2View <- whnfViewTC t2
            case t2View of
              App (Def fun2) elims2 | fun1 == fun2 -> do
                debug_ "** Could invert, and same heads, checking spines."
                equalSpine (Def fun1) ctx elims1 elims2
              _ -> do
                t2Head <- termHead =<< unviewTC t2View
                case t2Head of
                  Nothing -> do
                    debug_ "** Definition invertible but we don't have a clause head."
                    fallback t1
                  Just tHead | Just (Clause pats _) <- lookup tHead injClauses -> do
                    debug_ $ "** Inverting on" <+> PP.pretty tHead
                    -- Make the eliminators match the patterns
                    matched <- matchPats pats elims1
                    -- And restart, if we matched something.
                    if matched
                      then do
                        debug_ $ "** Matched constructor, restarting"
                        checkEqual (ctx, type_, t1, t2)
                      else do
                        debug_ $ "** Couldn't match constructor"
                        fallback t1
                  Just _ -> do
                    checkError $ TermsNotEqual type_ t1 type_ t2
  where
    fallback t1 = return $ [(mvs, Unify ctx type_ t1 t2)]

    matchPats :: [Pattern] -> [Elim t] -> TC t s Bool
    matchPats (VarP : pats) (_ : elims) = do
      matchPats pats elims
    matchPats (ConP dataCon pats' : pats) (elim : elims) = do
      matched <- matchPat dataCon pats' elim
      (matched ||) <$> matchPats pats elims
    matchPats _ _ = do
      -- Less patterns than arguments is fine.
      --
      -- Less arguments than patterns is fine too -- it happens if we
      -- are waiting on some metavar which doesn't head an eliminator.
      return False

    matchPat :: Name -> [Pattern] -> Elim t -> TC t s Bool
    matchPat dataCon pats (Apply t) = do
      tView <- whnfViewTC t
      case tView of
        App (Meta mv) mvArgs -> do
          mvT <- instantiateDataCon mv dataCon
          void $ matchPat dataCon pats . Apply =<< eliminateTC mvT mvArgs
          return True
        Con dataCon' dataConArgs | dataCon == dataCon' ->
          matchPats pats (map Apply dataConArgs)
        _ -> do
          -- This can happen -- when we are blocked on metavariables
          -- that are impeding other definitions.
          return False
    matchPat _ _ _ = do
      -- Same as above.
      return False

equalSpine
  :: (IsTerm t)
  => Head -> Ctx t -> [Elim t] -> [Elim t] -> TC t s (Constraints t)
equalSpine h ctx elims1 elims2 = do
  hType <- headType ctx h
  checkEqualSpine ctx hType h elims1 elims2

checkEqualApplySpine
  :: (IsTerm t)
  => Ctx t -> Type t -> [Term t] -> [Term t]
  -> TC t s (Constraints t)
checkEqualApplySpine ctx type_ args1 args2 =
  checkEqualSpine' ctx type_ Nothing (map Apply args1) (map Apply args2)

checkEqualSpine
  :: (IsTerm t)
  => Ctx t -> Type t -> Head -> [Elim (Term t)] -> [Elim (Term t)]
  -> TC t s (Constraints t)
checkEqualSpine ctx type_ h elims1 elims2  = do
  h' <- appTC h []
  checkEqualSpine' ctx type_ (Just h') elims1 elims2

checkEqualSpine'
  :: (IsTerm t)
  => Ctx t -> Type t -> Maybe (Term t)
  -> [Elim (Term t)] -> [Elim (Term t)]
  -> TC t s (Constraints t)
checkEqualSpine' _ _ _ [] [] = do
  return []
checkEqualSpine' ctx type_ mbH (elim1 : elims1) (elim2 : elims2) = do
  let msg = do
        typeDoc <- prettyTermTC type_
        hDoc <- case mbH of
          Nothing -> return "No head"
          Just h  -> prettyTermTC h
        elims1Doc <- prettyElimsTC $ elim1 : elims1
        elims2Doc <- prettyElimsTC $ elim2 : elims2
        return $
          "*** checkEqualSpine" $$
          "type:" //> typeDoc $$
          "head:" //> hDoc $$
          "elims1:" //> elims1Doc $$
          "elims2:" //> elims2Doc
  debugBracket msg $ do
    case (elim1, elim2) of
      (Apply arg1, Apply arg2) -> do
        Pi dom cod <- whnfViewTC type_
        res1 <- checkEqual (ctx, dom, arg1, arg2)
        mbCod <- liftTermM $ strengthen_ 1 cod
        mbH' <- traverse (`eliminateTC` [Apply arg1]) mbH
        -- If the rest is non-dependent, we can continue immediately.
        case mbCod of
          Nothing -> do
            cod' <- liftTermM $ instantiate cod arg1
            return $ sequenceConstraints res1 (UnifySpine ctx cod' mbH' elims1 elims2)
          Just cod' -> do
            res2 <- checkEqualSpine' ctx cod' mbH' elims1 elims2
            return (res1 <> res2)
      (Proj proj projIx, Proj proj' projIx') | proj == proj' && projIx == projIx' -> do
          let Just h = mbH
          (h', type') <- applyProjection proj h type_
          checkEqualSpine' ctx type' (Just h') elims1 elims2
      _ ->
        checkError $ SpineNotEqual type_ (elim1 : elims1) type_ (elim1 : elims2)
checkEqualSpine' _ type_ _ elims1 elims2 = do
  checkError $ SpineNotEqual type_ elims1 type_ elims2

metaAssign
  :: (IsTerm t)
  => Ctx t -> Type t -> MetaVar -> [Elim (Term t)] -> Term t
  -> TC t s (Constraints t)
metaAssign ctx0 type0 mv elims0 t0 = do
  mvType <- getMetaVarType mv
  let msg = do
        mvTypeDoc <- prettyTermTC mvType
        elimsDoc <- prettyElimsTC elims0
        tDoc <- prettyTermTC t0
        return $
          "*** metaAssign" $$
          "assigning metavar:" <+> PP.pretty mv $$
          "of type:" //> mvTypeDoc $$
          "elims:" //> elimsDoc $$
          "to term:" //> tDoc
  debugBracket msg $ do
    -- Try to eta-expand the metavariable first.  If you can, eta-expand
    -- and restart the equality.  Otherwise, try to assign.
    (_, mvEndType) <- unrollPi mvType
    mbRecordDataCon <- runMaybeT $ do
      App (Def tyCon) _ <- lift $ whnfViewTC mvEndType
      Constant (Record dataCon _) _ <- lift $ getDefinition tyCon
      return dataCon
    case mbRecordDataCon of
      Just dataCon -> do
        let msg' = "*** Eta-expanding metavar " <+> PP.pretty mv <+>
                   "with datacon" <+> PP.pretty dataCon
        debugBracket_ msg' $ do
          mvT <- instantiateDataCon mv dataCon
          mvT' <- eliminateTC mvT elims0
          checkEqual (ctx0, type0, mvT', t0)
      Nothing -> do
        (ctx, elims, sub) <- etaExpandVars ctx0 elims0
        debug $ do
          -- TODO this check could be more precise
          if Ctx.length ctx0 == Ctx.length ctx
          then return "** No change in context"
          else do
            ctxDoc <- prettyContextTC ctx
            return $ "** New context:" //> ctxDoc
        type_ <- liftTermM $ sub type0
        t <- liftTermM $ sub t0
        debug $ do
          typeDoc <- prettyTermTC type_
          tDoc <- prettyTermTC t
          return $
            "** Type and term after eta-expanding vars:" $$
            "type:" //> typeDoc $$
            "term:" //> tDoc
        -- See if we can invert the metavariable
        ttInv <- invertMeta elims
        let invOrMvs = case ttInv of
              TTOK inv       -> Right inv
              TTMetaVars mvs -> Left $ HS.insert mv mvs
              -- TODO here we should also wait on metavars on the right that
              -- could simplify the problem.
              TTFail ()      -> Left $ HS.singleton mv
        case invOrMvs of
          Left mvs -> do
            debug_ $ "** Couldn't invert"
            -- If we can't invert, try to prune the variables not
            -- present on the right from the eliminators.
            t' <- nfTC t
            -- TODO should we really prune allowing all variables here?  Or
            -- only the rigid ones?
            fvs <- fvAll <$> freeVarsTC t'
            elims' <- mapM nf'TC elims
            mbMvT <- prune fvs mv elims'
            -- If we managed to prune them, restart the equality.
            -- Otherwise, wait on the metavariables.
            case mbMvT of
              Nothing -> do
                mvT <- metaVarTC mv elims
                return [(mvs, Unify ctx type_ mvT t)]
              Just mvT -> do
                mvT' <- eliminateTC mvT elims'
                checkEqual (ctx, type_, mvT', t')
          Right inv -> do
            debug $ do
              invDoc <- prettyInvertMetaTC inv
              return $
                "** Could invert, now pruning" $$
                "inversion:" //> invDoc
            t1 <- pruneTerm (Set.fromList $ invertMetaVars inv) t
            debug $ do
              t1Doc <- prettyTermTC t1
              return $ "** Pruned term:" //> t1Doc
            t2 <- applyInvertMeta inv t1
            case t2 of
              TTOK t' -> do
                mvs <- metaVarsTC t'
                when (mv `HS.member` mvs) $
                  checkError $ OccursCheckFailed mv t'
                instantiateMetaVar mv t'
                return []
              TTMetaVars mvs -> do
                debug_ ("** Inversion blocked on" //> PP.pretty (HS.toList mvs))
                mvT <- metaVarTC mv elims
                return [(mvs, Unify ctx type_ mvT t)]
              TTFail v ->
                checkError $ FreeVariableInEquatedTerm mv elims t v

-- | Eliminates projected variables by eta-expansion, thus modifying the
-- context.
etaExpandVars
  :: (IsTerm t)
  => Ctx t
  -- ^ Context we're in
  -> [Elim t]
  -- ^ Eliminators on the MetaVar
  -> TC t s (Ctx t, [Elim t], t -> TermM t)
  -- ^ Returns the new context, the new eliminators, and a substituting
  -- action to update terms to the new context.
etaExpandVars ctx0 elims0 = do
  elims1 <- mapM (etaContractElim <=< nf'TC) elims0
  let msg = do
        elimsDoc <- prettyElimsTC elims1
        return $
          "*** Eta-expand vars" $$
          "elims:" //> elimsDoc
  debugBracket msg $ do
    mbVar <- collectProjectedVar elims1
    case mbVar of
      Nothing ->
        return (ctx0, elims1, \t -> return t)
      Just (v, tyCon) -> do
        debug_ $ "** Found var" <+> PP.pretty v <+> "with tyCon" <+> PP.pretty tyCon
        let (ctx1, type_, tel) = splitContext ctx0 v
        (tel', sub) <- etaExpandVar tyCon type_ tel
        elims2 <- mapM (liftTermM . mapElimM sub) elims1
        (ctx2, elims3, sub') <- etaExpandVars (ctx1 Ctx.++ Tel.unTel tel') elims2
        return (ctx2, elims3, (sub >=> sub'))

-- | Expands a record-typed variable ranging over the given 'Tel.Tel',
-- returning a new telescope ranging over all the fields of the record
-- type and the old telescope with the variable substituted with a
-- constructed record, and a substitution for the old variable.
etaExpandVar
  :: (IsTerm t)
  => Name
  -- ^ The type constructor of the record type.
  -> Type t
  -- ^ The type of the variable we're expanding.
  -> Tel.Tel t
  -> TC t s (Tel.Tel t, t -> TermM t)
etaExpandVar tyCon type_ tel = do
  Constant (Record dataCon projs) _ <- getDefinition tyCon
  DataCon _ dataConTypeTel dataConType <- getDefinition dataCon
  App (Def _) tyConPars0 <- whnfViewTC type_
  let Just tyConPars = mapM isApply tyConPars0
  appliedDataConType <- liftTermM $ Tel.substs dataConTypeTel dataConType tyConPars
  (dataConPars, _) <- assert ("etaExpandVar, unrollPiWithNames:" <+>) $
    unrollPiWithNames appliedDataConType (map fst projs)
  dataConT <- conTC dataCon =<< mapM varTC (ctxVars dataConPars)
  tel' <- liftTermM $ Tel.subst 0 dataConT =<< Tel.weaken 1 1 tel
  let telLen = Tel.length tel'
  dataConT' <- liftTermM $ weaken_ telLen dataConT
  let sub t = subst telLen dataConT' =<< weaken (telLen + 1) 1 t
  return (dataConPars Tel.++ tel', sub)

compareTerms :: (IsTerm t) => CheckEqual t -> TC t s (Constraints t)
compareTerms (ctx, type_, t1, t2) = do
  typeView <- whnfViewTC type_
  t1View <- whnfViewTC t1
  t2View <- whnfViewTC t2
  let mkVar n ix = varTC $ V $ named n ix
  case (typeView, t1View, t2View) of
    -- Note that here we rely on canonical terms to have canonical
    -- types, and on the terms to be eta-expanded.
    (Pi dom cod, Lam body1, Lam body2) -> do
      -- TODO there is a bit of duplication between here and expansion.
      name <- getAbsNameTC body1
      ctx' <- extendContext ctx (name, dom)
      checkEqual (ctx', cod, body1, body2)
    (Set, Pi dom1 cod1, Pi dom2 cod2) -> do
      -- Pi : (A : Set) -> (A -> Set) -> Set
      piType <- do
        av <- mkVar "A" 0
        b <- piTC av set
        piTC set =<< piTC b set
      cod1' <- lamTC cod1
      cod2' <- lamTC cod2
      checkEqualApplySpine ctx piType [dom1, cod1'] [dom2, cod2']
    (Set, Equal type1' l1 r1, Equal type2' l2 r2) -> do
      -- _==_ : (A : Set) -> A -> A -> Set
      equalType_ <- do
        xv <- mkVar "A" 0
        yv <- mkVar "A" 1
        piTC set =<< piTC xv =<< piTC yv set
      checkEqualApplySpine ctx equalType_ [type1', l1, r1] [type2', l2, r2]
    (Equal _ _ _, Refl, Refl) -> do
      return []
    ( App (Def _) tyConPars0, Con dataCon dataConArgs1, Con dataCon' dataConArgs2) | dataCon == dataCon' -> do
       let Just tyConPars = mapM isApply tyConPars0
       DataCon _ dataConTypeTel dataConType <- getDefinition dataCon
       appliedDataConType <- liftTermM $ Tel.substs dataConTypeTel dataConType tyConPars
       checkEqualApplySpine ctx appliedDataConType dataConArgs1 dataConArgs2
    (Set, Set, Set) -> do
      return []
    (_, App h elims1, App h' elims2) | h == h' -> do
      equalSpine h ctx elims1 elims2
    (_, _, _) -> do
     checkError $ TermsNotEqual type_ t1 type_ t2


-- Pretty printing Constraints

prettyConstraintTC
  :: (IsTerm t) => Constraint t -> TC t s PP.Doc
prettyConstraintTC c = withSignatureTermM $ \sig -> prettyConstraint sig c

prettyConstraint
  :: (IsTerm t) => Sig.Signature t -> Constraint t -> TermM PP.Doc
prettyConstraint sig c0 = do
  case fromMaybe c0 (simplify c0) of
    Unify ctx type_ t1 t2 -> do
      ctxDoc <- prettyContext sig ctx
      typeDoc <- prettyTerm sig type_
      t1Doc <- prettyTerm sig t1
      t2Doc <- prettyTerm sig t2
      return $ group $
        ctxDoc <+> "|-" //
        group (t1Doc // hang 2 "=" // t2Doc // hang 2 ":" // typeDoc)
    c1 :>>: c2 -> do
      c1Doc <- prettyConstraint sig c1
      c2Doc <- prettyConstraint sig c2
      return $ group (group c1Doc $$ hang 2 ">>" $$ group c2Doc)
    Conj cs -> do
      csDoc <- mapM (prettyConstraint sig) cs
      return $
        "Conj" //> PP.list csDoc
    UnifySpine ctx type_ mbH elims1 elims2 -> do
      ctxDoc <- prettyContext sig ctx
      typeDoc <- prettyTerm sig type_
      hDoc <- case mbH of
        Nothing -> return "no head"
        Just h  -> prettyTerm sig h
      elims1Doc <- prettyElims sig elims1
      elims2Doc <- prettyElims sig elims2
      return $
        "UnifySpine" $$
        "ctx:" //> ctxDoc $$
        "type:" //> typeDoc $$
        "h:" //> hDoc $$
        "elims1:" //> elims1Doc $$
        "elims2:" //> elims2Doc
