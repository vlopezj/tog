module BadPostponing_red where

{-@AGDA-}
open import Prelude

--data _==_ {A : Set}(x : A) : A -> Set where
--  refl : x == x

data Bool : Set where
  true : Bool
  false : Bool

record Times (A : Set) (B : Set) : Set
record Times A B where
  constructor pair
  field
    fst : A
    snd : B

{-@AGDA-}
open Times

postulate f : (A : Set) -> A -> Bool

Foo : Bool -> Set
Foo true = Bool
Foo false = Bool

Alpha : Bool
Beta : Foo Alpha

test : f (Times Bool (Foo Alpha)) (pair Alpha Beta) == f (Times Bool Bool) (pair false false)

Alpha = _
Beta = Alpha
test = refl

-- Normalizing Alpha yields a metavariable, but normalizing Beta yields
-- false.
