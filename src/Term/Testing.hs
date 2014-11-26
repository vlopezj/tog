{-# OPTIONS_GHC -fno-warn-orphans #-}
module Term.Testing where

import           Prelude                          hiding (pi)

import           Prelude.Extended
import           Term                             hiding (lam, pi, equal, set, refl, con, app)
import           Term.Impl
import qualified Term                             as Term
import           Syntax
import qualified Syntax.Abstract                  as SA

type Tm = GraphReduce

run :: TermM Tm a -> IO a
run = runTermM sigEmpty

tm_ :: (MonadTerm Tm m) => SA.Expr -> m Tm
tm_ = tm []

tm :: forall m. (MonadTerm Tm m) => [Name] -> SA.Expr -> m Tm
tm nms e0 = case e0 of
  SA.Lam n e -> do
    Term.lam =<< tm (n : nms) e
  SA.Pi n dom cod -> do
    dom' <- tm nms dom
    cod' <- tm (n : nms) cod
    Term.pi_ dom' cod'
  SA.Fun dom cod -> do
    join $ Term.pi_ <$> tm nms dom
                    <*> (weaken_ 1 =<< tm nms cod)
  SA.Equal type_ x y -> do
    join $ Term.equal <$> tm nms type_ <*> tm nms x <*> tm nms y
  SA.Set _ -> do
    return Term.set
  SA.Refl _ -> do
    return Term.refl
  SA.Meta _ -> do
    error "tm.Meta"
  SA.Con dataCon es -> do
    join $ Term.con dataCon <$> mapM (tm nms) es
  SA.App h es -> do
    let h' = case h of
          SA.Var n -> case n `elemIndex` nms of
                        Nothing -> Def $ DKName n
                        Just i  -> Var $ mkVar n $ fromIntegral i
          SA.Def n -> Def $ DKName n
          SA.J _   -> J
    Term.app h' =<< mapM tmElim es
  where
    tmElim (SA.Proj _)   = error "tm.Proj"
    tmElim (SA.Apply impl e') = Apply <$> tm nms impl <*> tm nms e'

-- Abbreviations
------------------------------------------------------------------------

lam :: Name -> SA.Expr -> SA.Expr
lam = SA.Lam

pi :: Name -> SA.Expr -> SA.Expr -> SA.Expr
pi = SA.Pi

(-->) :: SA.Expr -> SA.Expr -> SA.Expr
(-->) = SA.Fun

equal :: SA.Expr -> SA.Expr -> SA.Expr -> SA.Expr
equal = SA.Equal

app :: SA.Head -> [SA.Expr] -> SA.Expr
app h = SA.App h . map (SA.Apply (SA.Top $ srcLoc h))

set :: SA.Expr
set = SA.Set SA.noSrcLoc

meta :: Name -> SA.Expr
meta n = SA.App (SA.Def n) []

proj :: Name -> SA.Expr
proj n = SA.App (SA.Def n) []

refl :: SA.Expr
refl = SA.Refl SA.noSrcLoc

con :: Name -> [SA.Expr] -> SA.Expr
con = SA.Con

instance IsString SA.Expr where
  fromString s = SA.App (SA.Var (fromString s)) []

instance IsString SA.Head where
  fromString s = SA.Var (fromString s)
