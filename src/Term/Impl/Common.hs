{-# LANGUAGE OverloadedStrings #-}
module Term.Impl.Common where

import           Prelude                          hiding (pi, foldr)

import           Bound                            (Var(B, F))
import qualified Bound.Name                       as Bound
import           Bound.Var                        (unvar)
import           Control.Applicative              (pure, (<*>), (<|>))
import           Control.Monad                    (msum, join)
import           Control.Monad.Trans              (lift)
import           Control.Monad.Trans.Maybe        (MaybeT(MaybeT), runMaybeT)
import           Data.Functor                     ((<$>))
import qualified Data.HashSet                     as HS
import           Data.Traversable                 (traverse)

import           Syntax.Internal                  (Name)
import           Term
import qualified Term.Signature                   as Sig

-- TODO remove duplication between this and the actual `eliminate'
-- | Tries to apply the eliminators to the term.  Trows an error
-- when the term and the eliminators don't match.
substEliminate
  :: (IsTerm t) => t v -> [Elim t v] -> TermM (t v)
substEliminate t elims = do
  tView <- view t
  case (tView, elims) of
    (_, []) ->
        return t
    (Con _c args, Proj _ field : es) ->
        if unField field >= length args
        then error "substEliminate: Bad elimination"
        else substEliminate (args !! unField field) es
    (Lam body, Apply argument : es) -> do
        body' <- instantiate body argument
        substEliminate body' es
    (App h es1, es2) ->
        app h (es1 ++ es2)
    (_, _) ->
        error $ "substEliminate: Bad elimination"

genericSubst
  :: (IsTerm t) => t a -> (a -> TermM (t b)) -> TermM (t b)
genericSubst t f = do
  tView <- view t
  case tView of
    Lam body ->
      lam =<< genericSubst body (lift' f)
    Pi dom cod ->
      join $ pi <$> subst dom f <*> subst cod (lift' f)
    Equal type_ x y  ->
      join $ equal <$> subst type_ f <*> subst x f <*> subst y f
    Refl ->
      return refl
    Con dataCon args ->
      join $ con dataCon <$> mapM (`subst` f) args
    Set ->
      return set
    App h els  -> do
      els' <- mapM (mapElimM (`subst` f)) els
      case h of
        Var v   -> do t' <- f v; substEliminate t' els'
        Def n   -> app (Def n) els'
        Meta mv -> app (Meta mv) els'
        J       -> app J els'
  where
    lift' :: (IsTerm t)
          => (a -> TermM (t b))
          -> (TermVar a -> TermM (Abs t b))
    lift' _ (B v) = var $ B v
    lift' g (F v) = substMap F =<< g v

genericWhnf
  :: (IsTerm t) => Sig.Signature t -> t v -> TermM (Blocked t v)
genericWhnf sig t = do
  tView <- view t
  case tView of
    App (Meta mv) es | Just t' <- Sig.getMetaVarBody sig mv -> do
      whnf sig =<< eliminate sig (substVacuous t') es
    App (Def defName) es | Function _ cs <- Sig.getDefinition sig defName -> do
      mbT <- whnfFun sig defName es $ ignoreInvertible cs
      case mbT of
        Just t' -> return t'
        Nothing -> return $ NotBlocked t
    App J (_ : x : _ : _ : Apply p : Apply refl' : es) -> do
      refl'' <- whnf sig refl'
      reflView <- view =<< ignoreBlocking refl''
      case reflView of
        Refl -> whnf sig =<< eliminate sig p (x : es)
        _    -> return $ NotBlocked t
    App (Meta mv) elims ->
      return $ MetaVarHead mv elims
    _ ->
      return $ NotBlocked t

whnfFun
  :: (IsTerm t)
  => Sig.Signature t
  -> Name -> [Elim t v] -> [Closed (Clause t)]
  -> TermM (Maybe (Blocked t v))
whnfFun _ _ _ [] = do
  return Nothing
whnfFun sig funName es (Clause patterns body : clauses) = runMaybeT $ do
  matched <- lift $ matchClause sig es patterns
  case matched of
    TTMetaVars mvs ->
      return $ BlockedOn mvs funName es
    TTFail () ->
      MaybeT $ whnfFun sig funName es clauses
    TTOK (args, leftoverEs) -> lift $ do
      body' <- instantiateClauseBody body args
      whnf sig =<< eliminate sig body' leftoverEs

matchClause
  :: (IsTerm t)
  => Sig.Signature t
  -> [Elim t v] -> [Pattern]
  -> TermM (TermTraverse () ([t v], [Elim t v]))
matchClause _ es [] =
  return $ pure ([], es)
matchClause sig (Apply arg : es) (VarP : patterns) = do
  matched <- matchClause sig es patterns
  return $ (\(args, leftoverEs) -> (arg : args, leftoverEs)) <$> matched
matchClause sig (Apply arg : es) (ConP dataCon dataConPatterns : patterns) = do
  blockedArg <- whnf sig arg
  case blockedArg of
    MetaVarHead mv _ -> do
      matched <- matchClause sig es patterns
      return $ TTMetaVars (HS.singleton mv) <*> matched
    NotBlocked t -> do
      tView <- view t
      case tView of
        Con dataCon' dataConArgs | dataCon == dataCon' ->
          matchClause sig (map Apply dataConArgs ++ es) (dataConPatterns ++ patterns)
        _ ->
          return $ TTFail ()
    _ ->
      return $ TTFail ()
matchClause _ _ _ =
  return $ TTFail ()

genericGetAbsName
  :: forall t v0.
     (IsTerm t)
  => Abs t v0 -> TermM (Maybe Name)
genericGetAbsName = go $ \v -> case v of
  B v' -> Just $ Bound.name v'
  F _  -> Nothing
  where
    lift' _ (B _) = Nothing
    lift' f (F v) = f v

    go :: (v -> Maybe Name) -> t v -> TermM (Maybe Name)
    go f t = do
      tView <- view t
      case tView of
        Lam body -> go (lift' f) body
        Pi dom cod -> (<|>) <$> go f dom <*> go (lift' f) cod
        Equal type_ x y -> msum <$> mapM (go f) [type_, x, y]
        Refl -> return Nothing
        Con _ args -> msum <$> mapM (go f) args
        Set -> return Nothing
        App h els -> do
          let mbN = case h of
                Var v -> f v
                _     -> Nothing
          ((mbN <|>) . msum) <$>
            mapM (foldElim (go f) (\_ _ -> return Nothing)) els

genericStrengthen
  :: (IsTerm t) => Abs t v -> TermM (Maybe (t v))
genericStrengthen = runMaybeT . go (unvar (const Nothing) Just)
  where
    lift' :: (v -> Maybe v0) -> (TermVar v -> Maybe (TermVar v0))
    lift' _ (B _) = Nothing
    lift' f (F v) = F <$> f v

    go :: (IsTerm t)
       => (v -> Maybe v0) -> t v -> MaybeT TermM (t v0)
    go f t = do
      tView <- lift $ view t
      case tView of
        Lam body -> do
          lift . lam =<< go (lift' f) body
        Pi dom cod -> do
          dom' <- go f dom
          cod' <- go (lift' f) cod
          lift $ pi dom' cod'
        Equal type_ x y  -> do
          type' <- go f type_
          x' <- go f x
          y' <- go f y
          lift $ equal type' x' y'
        Refl -> do
          return refl
        Con dataCon args -> do
          lift . con dataCon =<< mapM (go f) args
        Set -> do
          return set
        App h els -> do
          h' <- MaybeT $ return $ traverse f h
          els' <- mapM (mapElimM (go f)) els
          lift $ app h' els'

genericNf :: forall t v. (IsTerm t) => Sig.Signature t -> t v -> TermM (t v)
genericNf sig t = do
  tView <- whnfView sig t
  case tView of
    Lam body ->
      lam =<< nf sig body
    Pi domain codomain ->
      join $ pi <$> nf sig domain <*> nf sig codomain
    Equal type_ x y ->
      join $ equal <$> nf sig type_ <*> nf sig x <*> nf sig y
    Refl ->
      return refl
    Con dataCon args ->
      join $ con dataCon <$> mapM (nf sig) args
    Set ->
      return set
    App h elims ->
      join $ app h <$> mapM (nf' sig) elims