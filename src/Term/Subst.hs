{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
module Term.Subst
  ( -- * Type
    Subst
  , id
  , singleton
  , weaken
  , instantiate
  , strengthen
  , lift
    -- * Operations
  , chain
  , compose
  , lookup
  , null
  ) where

import           Prelude.Extended                 hiding (lift, length, lookup, (++), drop, id, null)
import           Term.Subst.Types
import           Term.Synonyms
import           Term.Types

-- Smart constructors
------------------------------------------------------------------------

id :: Subst t
id = Id

singleton :: (MonadTerm t m, IsTerm t) => Term t -> m (Subst t)
singleton t = instantiate t id

weaken :: Natural -> Subst t -> Subst t
weaken 0 rho            = rho
weaken n (Weaken m rho)     = Weaken (n + m) rho
weaken n (Strengthen m rho) = case n - m of
                                0         -> rho
                                k | k > 0 -> Weaken k rho
                                k         -> Strengthen k rho
weaken n rho                = Weaken n rho

strengthen :: Natural -> Subst t -> Subst t
strengthen 0 rho                = rho
strengthen n (Strengthen m rho) = Strengthen (m + n) rho
strengthen n (Weaken m rho)     = case n - m of
                                    0         -> rho
                                    k | k < 0 -> Strengthen k rho
                                    k         -> Weaken k rho
strengthen n rho                = Strengthen n rho

-- TODO here we could pattern match on the term and optimize away -- see
-- Agda.TypeChecking.Substitute
instantiate :: (MonadTerm t m, IsTerm t) => Term t -> Subst t -> m (Subst t)
instantiate t rho = do
  tView <- view t
  return $ case (tView, rho) of
    (App (Var v) [], Weaken m sgm) | varIndex v + 1 == m ->
      weaken (m-1) $ lift 1 sgm
    _ ->
      Instantiate t rho

lift :: Natural -> Subst t -> Subst t
lift n _            | n < 0 = error "lift.impossible"
lift 0 rho          = rho
lift _ Id           = Id
lift k (Lift n rho) = Lift (n + k) rho
lift k rho          = Lift k rho

null :: Subst t -> Bool
null Id = True
null _  = False

-- Operations
------------------------------------------------------------------------

drop :: Natural -> Subst t -> Subst t
drop n rho                 | n <= 0 = rho
drop n Id                  = weaken n id
drop n (Weaken m rho)      = weaken m (drop n rho)
drop n (Instantiate _ rho) = drop (n - 1) rho
drop n (Strengthen m rho)  = drop (n - m) rho
drop _ (Lift 0 _)          = error "drop.Lift"
drop n (Lift m rho)        = weaken 1 $ drop (n - 1) $ lift (m - 1) rho

chain
  :: (IsTerm t, MonadTerm t m)
  => Subst t -> Subst t -> m (Subst t)
chain = flip compose

compose
  :: (IsTerm t, MonadTerm t m)
  => Subst t -> Subst t -> m (Subst t)
compose rho Id =
  return rho
compose Id  rho =
  return rho
compose rho (Weaken n sgm) =
  compose (drop n rho) sgm
compose rho (Instantiate u sgm) =
  join $ instantiate <$> applySubst u rho <*> compose rho sgm
compose rho (Strengthen n sgm) =
  strengthen n <$> compose rho sgm
compose _ (Lift 0 _) =
  error "compose.Lift 0"
compose (Instantiate u rho) (Lift n sgm) =
  join $ instantiate u <$> compose rho (lift (n - 1) sgm)
compose rho (Lift n sgm) =
  join $ instantiate <$> lookup (boundVar "_") rho
                     <*> compose rho (weaken 1 (lift (n - 1) sgm))

lookup :: (IsTerm t, MonadTerm t m) => Var -> Subst t -> m (Term t)
lookup v0 rho0 = go rho0 (varIndex v0)
  where
    nm = varName v0

    go rho i = case rho of
      Id -> do
        var v
      Weaken n Id -> do
        let j = i + n
        var $ mkVar nm j
      Weaken n rho' -> do
        (`applySubst` weaken n id) =<< go rho' i
      Instantiate u rho' -> do
        if i == 0 then return u else go rho' (i - 1)
      Strengthen n rho' -> do
        let _assert@True = i >= n
        go rho' (i - n)
      Lift n rho' -> do
        if i < n
          then var v
          else (`applySubst` weaken n id) =<< go rho' (i - n)
      where
        v = mkVar nm i