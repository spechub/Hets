{- |
Module      :  $EmptyHeader$
Description :  <optional short description entry>
Copyright   :  (c) <Authors or Affiliations>
License     :  GPLv2 or higher

Maintainer  :  <email>
Stability   :  unstable | experimental | provisional | stable | frozen
Portability :  portable | non-portable (<reason>)

<optional description>
-}
module Main where

import System
import Syntax.AS_Library
import ATerm.AbstractSyntax
import Common.Result
import ATC.Sml_cats
import ATC.Grothendieck
import Driver.WriteLibDefn
import Driver.ReadFn
import Comorphisms.LogicList

main :: IO ()
main = getArgs >>= mapM_ testATC

testATC :: FilePath -> IO ()
testATC fp = do
  libdefn <- read_sml_ATerm fp
  ld1 <- readWriteATerm1 libdefn
  putStrLn $ show $ show libdefn == show ld1
  ld2 <- readWriteATerm2 libdefn
  putStrLn $ show $ show libdefn == show ld2

readWriteATerm1 :: LIB_DEFN -> IO LIB_DEFN
readWriteATerm1 ld  = do
    (att1, ix) <- toShATermLG' emptyATermTable ld
    return $ snd $ fromShATermLG' preLogicGraph ix att1

readWriteATerm2 :: LIB_DEFN -> IO LIB_DEFN
readWriteATerm2 ld  = do
    str <- toShATermString ld
    return $ maybe (error "readWriteATerm2")
                         id $ maybeResult $ fromShATermString preLogicGraph str
