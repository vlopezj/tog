{-# LANGUAGE DeriveAnyClass #-}
module Tog.Term.Impl.HashConsed where

import           Data.Default
import qualified Data.HashTable.IO                as HT
import           System.IO.Unsafe                 (unsafePerformIO)

import           Tog.Names
import           Tog.Term.Types
import           Tog.Term.Synonyms
import           Tog.Term.Impl.Common
import           Tog.Prelude

import           System.Mem.StableName

import           Control.Monad.Reader (ReaderT, ask, runReaderT)
import           Control.Monad.Writer (WriterT, tell, runWriterT)

import Data.Interned (Id, Interned(..), Cache, mkCache, intern, Uninternable(..))

type HashConsed = ITerm       

#if TogLazyHashConsed
data ITerm = IT { internalId :: {-# UNPACK #-} Id
                , internalCell :: TermView ITerm
                } deriving (Typeable, Show)
#elif TogStrictHashConsed
data ITerm = IT { internalId :: {-# UNPACK #-} !Id
                , internalCell :: TermView ITerm
                } deriving (Typeable, Show)
#endif            

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


makeStrictStableName :: (MonadIO m) => a -> m (StableName a)
makeStrictStableName a = a `seq` liftIO (makeStableName a)
  

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
  nf t = fst <$> do
    s <- askSignature
    let !s_v = sigVersion s
    sigLookupCache nfTermCache (internalId t) $ \case
      Nothing -> ((, sigVersion s) <$> lift (lift (genericNf t))) >>= yieldToCache
      Just (t',v) | sigVersionStale s v -> do
                      t'' <- lift$ lift$ genericNf t'
                      tell [(internalId t', (t'', s_v))]
                      yieldToCache (t'', s_v)
      Just (t',_) -> return (t', s_v)

instance PrettyM ITerm ITerm where
  prettyPrecM = genericPrettyPrecM

-- TODO: Memoize: Remove version check.
instance ApplySubst ITerm ITerm where
  safeApplySubst t sub = do
    subn <- makeStrictStableName sub
    sigLookupCache safeApplySubstCache (subn, internalId t) $ \case
      Nothing  -> lift (lift (genericSafeApplySubst t sub)) >>= yieldToCache 
      Just t'  -> return t'

instance SynEq ITerm ITerm where
  synEq x y = return (x == y)

-- Perhaps memoize
instance IsTerm ITerm where
  whnf t = do
    s <- askSignature
    sigLookupCache whnfTermCache (internalId t) $ \case
      Nothing -> (lift.lift) (genericWhnf t) >>= yieldToCache
      Just t' -> case t' of
        NotBlocked _ -> return t'
        BlockingHead mv _ -> do
          let b = sigMetaIsInstantiated s mv
          if b then do
            t''  <- lift$ lift$ ignoreBlocking t'
            t''' <- lift$ lift$ genericWhnf t''
            tell [(internalId t'', t''')]
            yieldToCache t'''
          else
            return t'

        BlockedOn mvs _ _ -> do
          case sigMetasAreInstantiated s mvs of
            -- No metas instantiated
            True  -> return t'
            -- Metas where instantiated
            False -> do
              t''  <- lift$ lift$ ignoreBlocking t'
              t''' <- lift$ lift$ genericWhnf t''
              tell [(internalId t'', t''')]
              yieldToCache t'''
          
     
  view = return . unintern
  unview = return . intern

  set = intern Set 
  refl = intern Refl

  {-# NOINLINE typeOfJ #-}
  typeOfJ = unsafePerformIO $ runTermM sigEmpty genericTypeOfJ

  type SignatureMixin ITerm = ITermCache

data ITermCache = ITermCache {
    whnfTermCache :: HT.CuckooHashTable Id (Blocked ITerm),
    nfTermCache :: HT.CuckooHashTable Id (ITerm, Int),
    -- TODO: Check interning substitution
    safeApplySubstCache :: HT.CuckooHashTable (StableName (Subst ITerm), Id) ITerm
    }

-- TODO: Check other hash table implement
type Versioned a b = HT.CuckooHashTable a b

yieldToCache :: (Monad m) => b -> ReaderT a (WriterT [(a,b)] m) b
yieldToCache b = do
  a <- ask
  tell [(a,b)]
  return b

sigLookupCache :: (MonadTerm ITerm m, Eq a, Hashable a) => (ITermCache -> HT.CuckooHashTable a b)
               -> a -> (Maybe b -> ReaderT a (WriterT [(a,b)] m) b)
               -> m b
sigLookupCache f a freshen = do
  table <- f <$> askSignatureMixin
  cached <- liftIO$ HT.lookup table a
  (b', rest) <- runWriterT$ flip runReaderT a$ freshen cached
  forM_ rest $ liftIO . (\(ea,eb) -> HT.insert table ea eb)
  return b'
  

{-# NOINLINE defaultITermCache #-}
defaultITermCache :: Bool -> ITermCache
defaultITermCache a = unsafePerformIO$ do
    whnfTermCache <- HT.new 
    safeApplySubstCache <- HT.new
    nfTermCache <- HT.new
    return$ if a then ITermCache {..} else undefined

instance Default (ITermCache) where
  def = defaultITermCache True

{-
lookupWhnfTerm :: MonadTerm ITerm m => ITerm -> m (Maybe ITerm)
lookupWhnfTerm t0 = do
  ITermCache{whnfTermCache} <- askSignatureMixin
  liftIO$ HT.lookup whnfTermCache (internalId t0)

insertWhnfTerm :: MonadTerm ITerm m => ITerm -> ITerm -> m ()
insertWhnfTerm t1 t2 = do
  ITermCache{whnfTermCache} <- askSignatureMixin
  liftIO$ HT.insert whnfTermCache (internalId t1) t2
-}
