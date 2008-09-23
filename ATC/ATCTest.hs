module Main where

import System
import Syntax.AS_Library
import Common.ATerm.Lib
import Common.Result
import ATC.Sml_cats
import Driver.WriteLibDefn
import Driver.ReadFn

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
    att0 <- newATermTable
    (att1, ix) <- toShATerm' att0 ld
    return $ snd $ fromShATerm' ix att1

readWriteATerm2 :: LIB_DEFN -> IO LIB_DEFN
readWriteATerm2 ld  = do
    str <- toShATermString ld
    return $ maybe (error "readWriteATerm2")
                         id $ maybeResult $ fromShATermString str
