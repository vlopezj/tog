module BadPostponing where

{-@AGDA-}
open import Prelude

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data Bool : Set where
  true : Bool
  false : Bool

record Sigma (A : Set) (B : A -> Set) : Set
record Sigma A B where
  constructor pair
  field
    fst : A
    snd : B fst

Times : Set -> Set -> Set
Times A B = Sigma A (\ _ -> B)

postulate f : (A : Set) -> A -> Bool

record Wrap (A : Set) : Set where
  constructor wrap
  field wrapped : A


data Bot : Set where
  {-@EMPTY-}


Foo : Bool -> Set
Foo true  = Bot
Foo false = Bot

Alpha : Bool
Stuck : Set
Stuck = Foo Alpha
Beta : Stuck

test : f (Times Bool (Wrap Nat)) (pair true (wrap zero)) == f (Times Stuck Stuck)
  (pair Beta Beta)
Alpha = _
Beta  = _
test  = refl
