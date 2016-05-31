module BadPostponingN where

{-@AGDA-}
open import Prelude

data Bool : Set where
  true : Bool
  false : Bool
  

data Unit : Set where 
  tt : Unit

data Bot : Set where
  {-@EMPTY-}

T : Bool -> Set
T true = Unit
T false = Bot

f : (x : T _) -> x == tt
f tt = refl 


