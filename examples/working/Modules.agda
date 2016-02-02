module Modules where

{-@AGDA-}
open import Prelude

module One where
  postulate
    A : Set
    foo : A

test1 : One.A
test1 = One.foo

-- test2 : One.A
-- test2 = foo
--   where
--     open One

-- module Dummy where
--   open One
-- 
--   test3 : A
--   test3 = foo

data List (A : Set) : Set
data List A where
  nil : List A
  cons : A -> List A -> List A

module Monoid (A : Set) (empty : A) (append : A -> A -> A) where
  concat : List A -> A
  concat nil         = empty
  concat (cons x xs) = append x (concat xs)

module Nat where
  data Nat : Set
  data Nat where
    zero : Nat
    suc : Nat -> Nat

  empty : Nat
  empty = zero

  append : Nat -> Nat -> Nat
  append zero n = n
  append (suc n) m = suc (append n m)

sum : List Nat.Nat -> Nat.Nat
sum = concat
  where
    open Monoid Nat.Nat Nat.empty Nat.append

module First (A : Set) where
  postulate foo : A

  module Second (B : Set) where
    postulate bar : A -> B

    module Third where
      quux : B
      quux = bar foo


module First' where
  postulate
    A : Set
    foo : A

  module Second' where
    postulate
      B : Set
      bar : A -> B

    module Third' where
      quux : B
      quux = bar foo

test3 : First'.Second'.B
test3 = First'.Second'.Third'.quux

module DefEq (A : Set) (_ : (A -> A) -> A -> A) where
  postulate foo : A

module Dummy1 (A : Set) where
  open DefEq A (\f -> f)

  bar : A
  bar = foo

module Dummy2 (A : Set) where
  open DefEq A (\f x -> f x)

  bar : A
  bar = foo

-- module Dummy3 (A : Set) where
--   module D1 = Dummy1 A
--   module D2 = Dummy2 A
-- 
--   test : D1.bar == D2.bar
--   test = refl
