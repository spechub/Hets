{- |
Module      :  $Header$
Copyright   :  (c) C. Maeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  non-portable (Logic)

test by reading sml aterms
-}

module Main where

import Syntax.AS_Library
import ATerm.AbstractSyntax
import Common.Result
import ATC.Sml_cats
import ATC.Grothendieck
import Driver.WriteLibDefn
import Driver.ReadFn
import Comorphisms.LogicList
import Data.Maybe
import System.Environment

main :: IO ()
main = getArgs >>= mapM_ testATC

testATC :: FilePath -> IO ()
testATC fp = do
  libdefn <- read_sml_ATerm fp
  ld1 <- readWriteATerm1 libdefn
  print $ show libdefn == show ld1
  ld2 <- readWriteATerm2 libdefn
  print $ show libdefn == show ld2

readWriteATerm1 :: LIB_DEFN -> IO LIB_DEFN
readWriteATerm1 ld = do
    (att1, ix) <- toShATermLG' emptyATermTable ld
    return $ snd $ fromShATermLG' preLogicGraph ix att1

readWriteATerm2 :: LIB_DEFN -> IO LIB_DEFN
readWriteATerm2 ld = do
    str <- toShATermString ld
    return $ fromMaybe (error "readWriteATerm2")
      $ maybeResult $ fromShATermString preLogicGraph str
