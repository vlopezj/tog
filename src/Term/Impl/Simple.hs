module Term.Impl.Simple (Simple) where

import           Data.Typeable                    (Typeable)

import           Term
import           Term.Impl.Common
import           System.IO.Unsafe                 (unsafePerformIO)

-- Base terms
------------------------------------------------------------------------

newtype Simple v = S {unS :: TermView Simple v}
    deriving (Typeable)


instance Subst Simple where
  var v = unview (App (Var v) [])

  subst = genericSubst

instance IsTerm Simple where
  termEq = genericTermEq
  strengthen = genericStrengthen
  getAbsName = genericGetAbsName

  whnf = genericWhnf
  nf = genericNf

  view = return . unS
  unview = return . S

  set = S Set
  refl = S Refl
  typeOfJ = typeOfJS

{-# NOINLINE typeOfJS #-}
typeOfJS :: Closed Simple
typeOfJS = unsafePerformIO genericTypeOfJ

