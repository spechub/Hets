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
  putStrLn $ show $ show libdefn == show (readWriteATerm libdefn)
  ld <- readWriteATerm' libdefn
  putStrLn $ show $ show libdefn == show ld


readWriteATerm :: LIB_DEFN -> LIB_DEFN
readWriteATerm ld  = let  att1 = fst $ toShATerm emptyATermTable ld
                     in fromShATerm att1

readWriteATerm' :: LIB_DEFN -> IO LIB_DEFN
readWriteATerm' ld  = do
    str <- toShATermString ld
    return $ maybe (error "readWriteATerm'")
                         id $ maybeResult $ fromShATermString str
