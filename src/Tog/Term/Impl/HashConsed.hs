{-# LANGUAGE DeriveAnyClass #-}
module Tog.Term.Impl.HashConsed where

import qualified Data.HashTable.IO                as HT
import           System.IO.Unsafe                 (unsafePerformIO)

import           Tog.Names
import           Tog.Term.Types
import           Tog.Term.Synonyms
import           Tog.Term.Impl.Common
import           Tog.Prelude

import Data.Interned (Id, Interned(..), Cache, mkCache, intern, Uninternable(..))

type HashConsed = ITerm       

data ITerm = IT { internalId :: {-# UNPACK #-} !Id
                , internalCell :: !(TermView ITerm)

                } deriving (Typeable, Show)

type UITerm = TermView ITerm 

instance Interned ITerm where
  type Uninterned ITerm = UITerm
  data Description ITerm =
      DPi {-# UNPACK #-} !(Type Id) {-# UNPACK #-} !(Abs (Type Id))
    | DLam {-# UNPACK #-} !(Abs Id)
    | DEqual {-# UNPACK #-} !(Type Id) {-# UNPACK #-} !(Term Id) {-# UNPACK #-} !(Term Id)
    | DRefl
    | DSet
    | DCon {-# UNPACK #-} !QName [Term Id] [Term Id]

    | DAppV {-# UNPACK #-} !Var [Elim Id]
    | DAppD {-# UNPACK #-} !QName [Term Id] [Elim Id]
    | DAppM {-# UNPACK #-} !Meta [Elim Id]
    | DAppJ [Elim Id]

  describe t = case t of
    Pi a b -> DPi (i a) (i b)
    Lam a  -> DLam (i a)
    Equal a b c -> DEqual (i a) (i b) (i c)
    Refl -> DRefl
    Set  -> DSet

    Con (Opened k a) b -> DCon k (fmap i a) (fmap i b)

    App (Var v) a -> DAppV v (fmap (fmap i) a)
    App (Def (Opened k a)) b -> DAppD k (fmap i a) (fmap (fmap i) b)
    App (Meta m) a -> DAppM m (fmap (fmap i) a)
    App J a -> DAppJ (fmap (fmap i) a)
    
    where
      i = internalId

  identify = IT
  cache = iTermCache

instance Uninternable ITerm where
  unintern = internalCell

{-# NOINLINE iTermCache #-}
iTermCache :: Cache ITerm
iTermCache = mkCache
           
deriving instance Generic (Description ITerm)
deriving instance Show (Description ITerm)
deriving instance Eq (Description ITerm)
deriving instance Hashable (Description ITerm)

instance Hashable ITerm where
  hashWithSalt s i = hashWithSalt s (internalId i)

instance Eq ITerm where
  a == b = internalId a == internalId b

-- TODO: Memoize 
instance Metas ITerm ITerm where
  metas = genericMetas

-- TODO: Memoize
instance Nf ITerm ITerm where
  nf = genericNf

-- TODO: Memoize
instance PrettyM ITerm ITerm where
  prettyPrecM = genericPrettyPrecM

-- TODO: Memoize
instance ApplySubst ITerm ITerm where
  safeApplySubst = genericSafeApplySubst

instance SynEq ITerm ITerm where
  synEq x y = return (x == y)


-- Perhaps memoize
instance IsTerm ITerm where
  whnf t = do
    t' <- fromMaybe t <$> liftIO (lookupWhnfTerm t)
    blockedT <- genericWhnf t'
    -- TODO don't do a full traversal for this check
    t'' <- ignoreBlocking blockedT
    unless (t == t'') $ liftIO $ do
      -- TODO do not add both if we didn't get anything the with
      -- `lookupWhnfTerm'.
      insertWhnfTerm t t''
      insertWhnfTerm t' t''
    return blockedT

  view = return . unintern
  unview = return . intern

  set = intern Set 
  refl = intern Refl

  {-# NOINLINE typeOfJ #-}
  typeOfJ = unsafePerformIO $ runTermM sigEmpty genericTypeOfJ

-- Table

type TableKey = Id

{-# NOINLINE hashedTable #-}
hashedTable :: HT.CuckooHashTable Id ITerm
hashedTable = unsafePerformIO HT.new

lookupWhnfTerm :: ITerm -> IO (Maybe ITerm)
lookupWhnfTerm t0 = do
  HT.lookup hashedTable (internalId t0)

insertWhnfTerm :: ITerm -> ITerm -> IO ()
insertWhnfTerm t1 t2 = HT.insert hashedTable (internalId t1) t2
