{-# LANGUAGE CPP #-}
{- |
Module      :  $Header$
Description :  wrapper module for changed IO handling since ghc-6.12.1
Copyright   :  (c) Christian Maeder DFKI GmbH 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

reading and writing files changed between ghc-6.10.4 and ghc-6.12.1 from
latin1 to utf8.

This module allows to continue reading and writing latin1 (HetCASL) files.
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
  ) where

import System.IO

data Enc = Latin1 | Utf8

readEncFile :: Enc -> String -> IO String
writeEncFile :: Enc -> String -> String -> IO ()

-- | set encoding of stdin and stdout
setStdEnc :: Enc -> IO ()

#if __GLASGOW_HASKELL__ < 612
readEncFile _ = readFile
writeEncFile _ = writeFile
setStdEnc _ = return ()
#else
readEncFile c f = case c of
  Utf8 -> readFile f
  Latin1 -> do
        hdl <- openFile f ReadMode
        hSetEncoding hdl latin1
        hGetContents hdl

writeEncFile c f txt = case c of
  Utf8 -> writeFile f txt
  Latin1 -> withFile f WriteMode $ \ hdl -> do
      hSetEncoding hdl latin1
      hPutStr hdl txt

setStdEnc c = case c of
  Utf8 -> return ()
  Latin1 -> do
    hSetEncoding stdin latin1
    hSetEncoding stdout latin1
#endif
