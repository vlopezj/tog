{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
module Tog.Instrumentation.Debug
  ( -- * Init
    debugInit
    -- * API
  , DebugLabel
  , debugBracket
  , debugBracket_
  , debug
  , debug_
  , whenDebug
  , fatalError
  , stackTrace
  , printStackTrace
  ) where

import           Data.IORef                       (IORef, newIORef, readIORef, writeIORef)
import           System.IO.Unsafe                 (unsafePerformIO)

import           Tog.Instrumentation.Conf
import           Tog.Instrumentation.Timing
import           Tog.Prelude
import           Tog.PrettyPrint                  as PP

type DebugLabel = String

data DebugFrame = DebugFrame
  { dfDoc   :: !PP.Doc
  , dfLabel :: !DebugLabel
  }

_dummy :: a
_dummy = error "UNUSED" dfDoc

instance PP.Pretty DebugFrame where
  pretty (DebugFrame doc label) = "***" <+> PP.text label $$ doc

type DebugStack = [DebugFrame]

{-# NOINLINE stackRef #-}
stackRef :: IORef (Maybe DebugStack)
stackRef = unsafePerformIO $ newIORef Nothing

_ERROR_INDENT :: Natural
_ERROR_INDENT = 2

debugInit :: (MonadIO m) => m ()
debugInit = do
  conf <- readConf
  writeStackRef $ if confDebug conf then Just [] else Nothing

rawDebug :: (MonadIO m) => DebugStack -> PP.Doc -> PP.Doc -> m String
rawDebug stack label doc = do
  let s  = PP.renderPretty 100 $ label $$ doc
  let pad = replicate (length stack * _ERROR_INDENT) ' '
  return $ unlines $ map (pad ++) $ lines s

printRawDebug :: (MonadIO m) => DebugStack -> PP.Doc -> PP.Doc -> m ()
printRawDebug stack label doc =
  liftIO . hPutStr stderr =<< rawDebug stack label doc

matchLabel :: (MonadIO m) => DebugLabel -> m () -> m ()
matchLabel label m = do
  debugLabels <- confDebugLabels `liftM` readConf
  case debugLabels of
    DLAll                       -> m
    DLSome ls | label `elem` ls -> m
    _                           -> return ()

readStackRef :: (MonadIO m) => m (Maybe DebugStack)
readStackRef = liftIO $ readIORef stackRef

writeStackRef :: (MonadIO m) => Maybe DebugStack -> m ()
writeStackRef mbStack = liftIO $ writeIORef stackRef mbStack

debugBracket :: (MonadIO m) => DebugLabel -> m PP.Doc -> m a -> m a
debugBracket label docM m = do
  mbStack <- readStackRef
  forM_ mbStack $ \stack -> do
    doc <- docM
    matchLabel label $ printRawDebug stack ("***" <+> PP.text label) doc
    let frame = DebugFrame doc label
    writeStackRef $ Just $ frame : stack
  timing <- confTimeSections `liftM` readConf
  x <- if timing then timingBracket label m else m
  mbStack' <- readStackRef
  forM_ mbStack' $ \(_:stack) -> writeStackRef $ Just stack
  return x

debugBracket_ :: (MonadIO m) => DebugLabel -> PP.Doc -> m a -> m a
debugBracket_ label doc = debugBracket label (return doc)

debug :: (MonadIO m) => PP.Doc -> m PP.Doc -> m ()
debug label docM = do
  mbStack <- readStackRef
  forM_ mbStack $ \stack -> case stack of
    frame : _ -> do
      matchLabel (dfLabel frame) $ do
        doc <- docM
        printRawDebug stack ("**" <+> label) doc
    [] -> do
      return ()

debug_ :: (MonadIO m) => PP.Doc -> PP.Doc -> m ()
debug_ label doc = debug label (return doc)

whenDebug :: (MonadIO m) => m () -> m ()
whenDebug m = do
  mbStack <- readStackRef
  forM_ mbStack $ \_ -> m

renderStackTrace :: PP.Doc -> DebugStack -> PP.Doc
renderStackTrace err stack =
  "error:" //> err $$
  "stack trace:" //> PP.indent _ERROR_INDENT (PP.vcat (map PP.pretty stack))

stackTrace :: (MonadIO m) => PP.Doc -> PP.Doc -> m (Maybe String)
stackTrace heading err = do
  mbStack <- readStackRef
  forM mbStack $ \stack ->
    rawDebug [] ("***" <+> heading) (renderStackTrace err stack)

printStackTrace :: (MonadIO m) => PP.Doc -> PP.Doc -> m ()
printStackTrace heading err = do
  mbS <- stackTrace heading err
  liftIO $ forM_ mbS $ hPutStrLn stderr

{-# NOINLINE fatalError #-}
fatalError :: String -> a
fatalError s =
  let mbS = unsafePerformIO $ stackTrace "fatalError" $ PP.string s
  in case mbS of
       Nothing -> error $ "\nfatalError\n" ++ s
       Just s' -> error $ "\n" ++ s'
