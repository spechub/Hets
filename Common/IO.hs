{-# LANGUAGE CPP #-}
{- |
Module      :  ./Common/IO.hs
Description :  wrapper module for changed IO handling since ghc-6.12.1
Copyright   :  (c) Christian Maeder DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

reading and writing files changed between ghc-6.10.4 and ghc-6.12.1 from
latin1 to utf8.

This module allows to continue reading and writing latin1 (DOL) files.
However, this module does not support to write utf8 files with ghc-6.10.4 or
earlier versions.

The encoding only effects the contents. The encoding of file names is always
utf8.
-}

module Common.IO
  ( Enc (..)
  , readEncFile
  , writeEncFile
  , setStdEnc
  , catchIOException
  ) where

import System.IO
import Control.Exception as Exception

catchIOException :: a -> IO a -> IO a
catchIOException d a = catchJust (\ e ->
  fromException e :: Maybe IOException) a . const $ return d

data Enc = Latin1 | Utf8 deriving Show

readEncFile :: Enc -> String -> IO String
writeEncFile :: Enc -> String -> String -> IO ()

-- | set encoding of stdin and stdout
setStdEnc :: Enc -> IO ()

#if __GLASGOW_HASKELL__ < 612
readEncFile _ = readFile
writeEncFile _ = writeFile
setStdEnc _ = return ()
#else
readEncFile c f = do
  hdl <- openFile f ReadMode
  hSetEncoding hdl $ case c of
    Utf8 -> utf8
    Latin1 -> latin1
  hGetContents hdl

writeEncFile c f txt = withFile f WriteMode $ \ hdl -> do
    hSetEncoding hdl $ case c of
      Utf8 -> utf8
      Latin1 -> latin1
    hPutStr hdl txt

setStdEnc c = do
  hSetEncoding stdin $ case c of
    Utf8 -> utf8
    Latin1 -> latin1
  hSetEncoding stdout $ case c of
    Utf8 -> utf8
    Latin1 -> latin1
#endif
