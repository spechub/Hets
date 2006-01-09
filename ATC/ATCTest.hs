module Main where

import System
import Syntax.AS_Library
import Common.ATerm.Lib
import Common.Result
import ATC.AS_Library()
import ATC.Sml_cats
import Driver.WriteFn
import Driver.ReadFn

main :: IO ()
main = do args <- getArgs
          mapM_ testATC args

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
    (att1, _) <- toShATerm' att0 ld
    return $ fromShATerm att1

readWriteATerm2 :: LIB_DEFN -> IO LIB_DEFN
readWriteATerm2 ld  = do
    str <- toShATermString ld
    return $ maybe (error "readWriteATerm'")
                         id $ maybeResult $ fromShATermString str
