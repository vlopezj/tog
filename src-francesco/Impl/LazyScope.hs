module Impl.LazyScope (LazyScope) where

import Prelude                                    hiding (pi, abs, foldr)

import           Bound                            hiding (instantiate)
import           Bound.Name                       (instantiateName)
import           Prelude.Extras                   (Eq1, (==#))
import           Data.Foldable                    (Foldable, foldr)
import           Data.Traversable                 (Traversable, sequenceA)
import           Data.Functor                     ((<$>))
import           Control.Monad.Trans              (lift)
import           Control.Monad.Trans.Maybe        (MaybeT, runMaybeT)
import           Control.Monad                    (guard, mzero)
import           Data.Void                        (vacuous)
import           Data.Monoid                      ((<>), mconcat, mempty)

import           Types.Monad
import           Types.Definition
import           Types.Term
import           Types.Var

-- Base terms
------------------------------------------------------------------------

newtype LazyScope v = LS {unLS :: TermView LazyScope v}
    deriving (Eq, Eq1, Functor, Foldable, Traversable)

instance Monad LazyScope where
    return v = LS (App (Var v) [])

    LS term0 >>= f = LS $ case term0 of
        Lam body           -> Lam (LSAbs (unLSAbs body >>>= f))
        Pi domain codomain -> Pi (domain >>= f) (LSAbs (unLSAbs codomain >>>= f))
        Equal type_ x y    -> Equal (type_ >>= f) (x >>= f) (y >>= f)
        Set                -> Set
        App h elims        ->
            let elims' = map (>>>= f) elims
            in case h of
                   Var v   -> unLS $ eliminate (f v) elims'
                   Def n   -> App (Def n)   elims'
                   Con n   -> App (Con n)   elims'
                   J       -> App J         elims'
                   Refl    -> App Refl      elims'
                   Meta mv -> App (Meta mv) elims'

instance IsTerm LazyScope where
    newtype Abs LazyScope v = LSAbs {unLSAbs :: Scope (Named ()) LazyScope v}

    toAbs   = LSAbs . toScope
    fromAbs = fromScope . unLSAbs

    weaken = LSAbs . Scope .  return . F

    instantiate abs t = instantiate1 t (unLSAbs abs)

    abstract v = LSAbs . Bound.abstract f
      where
        f v' = if v == v' then Just (named (varName v) ()) else Nothing

    unview = LS
    view   = unLS

    eliminate (LS term0) elims = case (term0, elims) of
        (t, []) ->
            LS t
        (App (Con _c) args, Proj _ field : es) ->
            if unField field >= length args
            then error "Impl.Term.eliminate: Bad elimination"
            else case (args !! unField field) of
                   Apply t -> eliminate t es
                   _       -> error "Impl.Term.eliminate: Bad constructor argument"
        (Lam body, Apply argument : es) ->
            eliminate (instantiate body argument) es
        (App h es1, es2) ->
            LS $ App h (es1 ++ es2)
        (_, _) ->
            error "Impl.Term.eliminate: Bad elimination"

    whnf :: LazyScope v -> TC LazyScope v (LazyScope v)
    whnf ls@(LS t) = case t of
        App (Meta mv) es -> do
            mvInst <- getBodyOfMetaVar mv
            case mvInst of
              Nothing -> return ls
              Just t' -> whnf $ eliminate (vacuous t') es
        App (Def defName) es -> do
            def' <- getDefinition defName
            case def' of
              Function _ _ cs -> whnfFun ls es cs
              _               -> return ls
        App J (_ : x : _ : _ : Apply p : Apply (LS (App Refl [])) : es) ->
            whnf $ eliminate p (x : es)
        _ ->
            return ls
      where
        whnfFun
            :: LazyScope v -> [Elim LazyScope v] -> [Clause LazyScope]
            -> TC LazyScope v (LazyScope v)
        whnfFun ls' es clauses0 = case clauses0 of
            [] ->
                return ls'
            (Clause patterns body : clauses) -> do
                mbMatched <- runMaybeT $ matchClause es patterns
                case mbMatched of
                    Nothing ->
                        whnfFun ls' es clauses
                    Just (args, leftoverEs) -> do
                        let body' = instantiateName (args !!) (vacuous body)
                        whnf $ eliminate body' leftoverEs

        matchClause
            :: [Elim LazyScope v] -> [Pattern]
            -> MaybeT (TC LazyScope v) ([LazyScope v], [Elim LazyScope v])
        matchClause es [] =
            return ([], es)
        matchClause (Apply arg : es) (VarP : patterns) = do
            (args, leftoverEs) <- matchClause es patterns
            return (arg : args, leftoverEs)
        matchClause (Apply arg : es) (ConP dataCon dataConPatterns : patterns) = do
            LS (App (Con dataCon') dataConEs) <- lift $ whnf arg
            guard (dataCon == dataCon')
            matchClause (dataConEs ++ es) (dataConPatterns ++ patterns)
        matchClause _ _ =
            mzero

    metaVars t = case view t of
        Lam body           -> metaVars $ unscope $ unLSAbs $ body
        Pi domain codomain -> metaVars domain <> metaVars (unscope (unLSAbs (codomain)))
        Equal type_ x y    -> metaVars type_ <> metaVars x <> metaVars y
        App h elims        -> metaVarsHead h <> mconcat (map metaVarsElim elims)
        Set                -> mempty



-- TODO There seems to be a bug preventing us from deriving this.  Check
-- with 7.8.

instance Eq1 (Abs LazyScope) where
    LSAbs s1 ==# LSAbs s2 = s1 ==# s2

instance Functor (Abs LazyScope) where
    fmap f (LSAbs s) = LSAbs $ fmap f s

-- TODO instantiate all the methods
instance Foldable (Abs LazyScope) where
    foldr f x (LSAbs s) = foldr f x s

-- TODO instantiate all the methods
instance Traversable (Abs LazyScope) where
    sequenceA (LSAbs s) = LSAbs <$> sequenceA s
