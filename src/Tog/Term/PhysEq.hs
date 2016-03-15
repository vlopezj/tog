module Tog.Term.PhysEq (physEq) where

import System.Mem.StableName (makeStableName)
import System.IO.Unsafe (unsafePerformIO)

physEq :: (Monad m) => a -> a -> m Bool
physEq a b = return $ unsafePerformIO $ do
  sa <- makeStableName a
  sb <- makeStableName b
  return$ sa == sb

