module Prelude.Extended
  ( Foldable
  , Traversable
  , Hashable
  , hash
  , (<*>)
  , Applicative
  , (<>)
  , mempty
  , mconcat
  , (<$>)
  , (>=>)
  , (<=<)
  , Typeable
  , Generic
  , fromMaybe
  , pure
  , join
  , foldl'
  , liftM
  , when
  , void
  , guard
  , mzero
  , forM
  , msum
  , unless
  , first
  , forM_
  , on
  , sortBy
  , groupBy
  , isJust
  , comparing
  , traverse
  , (<$)
  , sequenceA
  , lift
  , trace
  , traceM
  , (<|>)
  , ap
  ) where

import Control.Applicative
import Control.Arrow
import Control.Monad hiding (forM_, msum, forM)
import Data.Foldable
import Data.Function
import Data.Hashable
import Data.List hiding (foldl')
import Data.Maybe
import Data.Monoid
import Data.Ord
import Data.Traversable
import Data.Typeable
import GHC.Generics
import Control.Monad.Trans
import Debug.Trace