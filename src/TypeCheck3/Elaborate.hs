{-# LANGUAGE OverloadedStrings #-}
module TypeCheck3.Elaborate
  ( elaborate
  ) where

import           Prelude.Extended
import qualified Syntax.Internal                  as A
import           Term
import           Term.Context                     (Ctx)
import qualified Term.Context                     as Ctx
import qualified Term.Telescope                   as Tel
import           TypeCheck3.Common
import           TypeCheck3.Monad
import           PrettyPrint                      (($$), (//>), render)
import qualified PrettyPrint                      as PP

elaborate
  :: (IsTerm t) => Ctx t -> Type t -> A.Expr -> TC t s (Term t, Constraint t)
elaborate ctx type_ absT = atSrcLoc absT $ do
  let msg = do
        typeDoc <- prettyTermTC type_
        let absTDoc = PP.pretty absT
        return $
          "*** elaborate" $$
          "type:" //> typeDoc $$
          "t:" //> absTDoc
  debugBracket msg $ do
    mvT <- addMetaVarInCtx ctx type_
    let waitForUnifiedType' type' t = waitForUnifiedType ctx type_ type' mvT t
    case absT of
      A.Set _ -> do
        return (mvT, waitForUnifiedType' set set)
      A.Pi name synDom synCod -> do
        (dom, constrDom) <- elaborate ctx set synDom
        (cod, constrCod) <- elaborate (Ctx.Snoc ctx (name, dom)) set synCod
        t <- piTC dom cod
        return (mvT, Conj [waitForUnifiedType' set t, constrDom, constrCod])
      A.Fun synDom synCod -> do
        elaborate ctx type_ (A.Pi "_" synDom synCod)
      A.Meta _ ->
        return (mvT, Conj [])
      A.Equal synType synT1 synT2 -> do
        (type', constrType) <- elaborate ctx set synType
        (t1, constrT1) <- elaborate ctx type' synT1
        (t2, constrT2) <- elaborate ctx type' synT2
        t <- equalTC type' t1 t2
        return (mvT, Conj [waitForUnifiedType' set t, constrType, constrT1, constrT2])
      A.Lam name synBody -> do
        dom <- addMetaVarInCtx ctx set
        let ctx' = Ctx.Snoc ctx (name, dom)
        cod <- addMetaVarInCtx ctx' set
        (body, constrBody) <- elaborate ctx' cod synBody
        type' <- piTC dom cod
        t <- lamTC body
        return (mvT, Conj [waitForUnifiedType' type' t, constrBody])
      A.Refl _ -> do
        eqType <- addMetaVarInCtx ctx set
        t1 <- addMetaVarInCtx ctx eqType
        type' <- equalTC eqType t1 t1
        return (mvT, waitForUnifiedType' type' refl)
      A.Con dataCon synArgs -> do
        DataCon tyCon tyConParsTel dataConType <- getDefinition dataCon
        tyConType <- definitionType =<< getDefinition tyCon
        tyConArgs <- fillArgsWithMetas ctx tyConType
        appliedDataConType <- liftTermM $ Tel.substs tyConParsTel dataConType tyConArgs
        (dataConArgs, constrDataConArgs) <- elaborateDataConArgs ctx appliedDataConType synArgs
        type' <- appTC (Def tyCon) $ map Apply tyConArgs
        t <- conTC dataCon dataConArgs
        return (mvT, Conj (waitForUnifiedType' type' t : constrDataConArgs))
      A.App h elims -> do
        elaborateApp ctx type_ h (reverse elims)

fillArgsWithMetas :: IsTerm t => Ctx t -> Term t -> TC t s [Term t]
fillArgsWithMetas ctx' type' = do
  typeView <- whnfViewTC type'
  case typeView of
    Pi dom cod -> do
      domName <- getAbsNameTC cod
      arg <- addMetaVarInCtx ctx' dom
      let ctx'' = Ctx.Snoc ctx' (domName, arg)
      (arg :) <$> fillArgsWithMetas ctx'' cod
    Set -> do
      return []
    _ -> do
      error "impossible.fillArgsWithMetas: bad type for tycon"

waitForUnifiedType
  :: IsTerm (Term t)
  => Ctx t
  -> Term t
  -- ^ When this type...
  -> Type t
  -- ^ ..is unified with this type...
  -> Term t
  -- ^ ..unify this term...
  -> Term t
  -- ^ ..with this term.
  -> Constraint t
waitForUnifiedType ctx type_ type' mvT t =
  Unify ctx set type' type_ :>>: Unify ctx type_ mvT t

elaborateDataConArgs
  :: (IsTerm t) => Ctx t -> Type t -> [A.Expr] -> TC t s ([Term t], [Constraint t])
elaborateDataConArgs _ _ [] =
  return ([], [])
elaborateDataConArgs ctx type_ (synArg : synArgs) = do
  Pi dom cod <- whnfViewTC type_
  (arg, constrArg) <- elaborate ctx dom synArg
  cod' <- instantiateTC cod arg
  (args, constrArgs) <- elaborateDataConArgs ctx cod' synArgs
  return (arg : args, constrArg : constrArgs)

inferHead
  :: (IsTerm t)
  => Ctx t -> A.Head -> TC t s (Term t, Type t)
inferHead ctx synH = atSrcLoc synH $ case synH of
  A.Var name -> do
    mbV <- liftTermM $ Ctx.lookupName name ctx
    case mbV of
      Nothing -> do
        checkError $ NameNotInScope name
      Just (v, type_) -> do
        h <- appTC (Var v) []
        return (h, type_)
  A.Def name -> do
    type_ <- definitionType =<< getDefinition name
    h <- appTC (Def name) []
    return (h, type_)
  A.J{} -> do
    h <- appTC J []
    return (h, typeOfJ)

elaborateApp
  :: (IsTerm t)
  => Ctx t -> Type t -> A.Head -> [A.Elim] -> TC t s (Term t, Constraint t)
elaborateApp ctx type_ h [] = do
  (t, hType) <- inferHead ctx h
  mvT <- addMetaVarInCtx ctx type_
  return (mvT, waitForUnifiedType ctx type_ hType mvT t)
elaborateApp ctx type_ h (A.Apply arg : elims) = do
  dom <- addMetaVarInCtx ctx set
  -- TODO better name here
  cod <- addMetaVarInCtx (Ctx.Snoc ctx ("_", dom)) set
  typeF <- piTC dom cod
  (f, constrF) <- elaborateApp ctx typeF h elims
  (arg', constrArg) <- elaborate ctx dom arg
  type' <- instantiateTC cod arg'
  t <- eliminateTC f [Apply arg']
  mvT <- addMetaVarInCtx ctx type_
  return (mvT, Conj [waitForUnifiedType ctx type_ type' mvT t, constrF, constrArg])
elaborateApp ctx type_ h (A.Proj proj : elims) = do
  Projection projIx tyCon projTypeTel projType <- getDefinition proj
  tyConType <- definitionType =<< getDefinition tyCon
  tyConArgs <- fillArgsWithMetas ctx tyConType
  typeRec <- appTC (Def tyCon) (map Apply tyConArgs)
  (rec_, constrRec) <- elaborateApp ctx typeRec h elims
  type0 <- liftTermM $ Tel.substs projTypeTel projType tyConArgs
  Pi _ type1 <- whnfViewTC type0
  type' <- instantiateTC type1 rec_
  t <- eliminateTC rec_ [Proj proj projIx]
  mvT <- addMetaVarInCtx ctx type_
  return (mvT, Conj [waitForUnifiedType ctx type_ type' mvT t, constrRec])