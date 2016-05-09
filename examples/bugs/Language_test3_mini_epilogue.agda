------------------------------------------------------------------------
-- A small definition of a dependently typed language, using the
-- technique from McBride's "Outrageous but Meaningful Coincidences"
------------------------------------------------------------------------

{-# OPTIONS --type-in-type #-}

module Language_test3_mini_epilogue where

------------------------------------------------------------------------
-- Prelude

{-@AGDA-}
open import Prelude

open import Language_test3_mini_prologue

raw-category : Type empty (\ _ -> raw-categoryU)
raw-category =
     -- Objects.
   sigma' set'
     -- Morphisms.
    (el' (var zero))
   --(pi' (el' (var zero)) set')
  -- (pi' (el' (var (suc zero))) set'))
  -- (sigma' (pi' (el' (var zero)) (pi' (el' (var (suc zero))) set'))

  --    -- Identity.
  -- (pi' (el' (var (suc zero)))
  --      (el' (app (app (var (suc zero)) (var zero)) (var zero)))))
