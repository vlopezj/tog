module BadPostponing where

{-@AGDA-}
open import Prelude

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data Bool : Set where
  true : Bool
  false : Bool

data Times (A : Set) (B : Set) : Set where
  pair : A -> B -> Times A B

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

Stuck : _
Stuck = Foo Alpha

Beta : Stuck

test : f (Times Bool (Wrap Nat)) (pair true (wrap zero)) == f (Times Stuck Stuck) (pair Beta Beta)
Alpha = _
Beta  = _
test  = refl
