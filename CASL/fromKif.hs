{- |
Module      :  $Header$
Copyright   :  (c) C.Maeder, Uni Bremen 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable 

convert .kif to .casl
-}
module Main where

import CASL.Kif
import CASL.Kif2CASL
import CASL.Sign
import CASL.AS_Basic_CASL
import CASL.Print_AS_Basic()

import Common.Utils
import Common.GlobalAnnotations
import Common.PrettyPrint
import Common.Lib.Pretty
import Common.AS_Annotation

import Text.ParserCombinators.Parsec
import System.Environment

main :: IO ()
main = getArgs >>= mapM_ process

process :: String -> IO ()
process s = do 
  e <- parseFromFile kifProg s 
  case e of 
    Left err -> putStrLn $ show err
    Right l -> do 
        let f = fst (stripSuffix [".kif"] s) ++ ".casl"
            (sign, sens) = kif2CASL l
            pp :: PrettyPrint a => a -> Doc
            pp = printText0 emptyGlobalAnnos
            d = pp sign $+$ vcat (map pp sens) 
        writeFile f $ shows d "\n"
  
