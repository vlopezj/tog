module EmptyPattern where

data Empty : Set where
  {-@EMPTY-}

absurd : Empty -> (A : Set) -> A
absurd () _
