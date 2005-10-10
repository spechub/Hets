{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  non-portable 

test the programatica parser and (HatAna) analysis

-}

module Main where

import Haskell.HatParser
import Haskell.HatAna
import Haskell.PreludeString
import ParseMonad
import PropLexer
import PropParser as HP
import PropPosSyntax

import System.Environment

import Common.Result
import Common.Print_AS_Annotation()
import Common.GlobalAnnotations
import Common.PrettyPrint

main :: IO ()
main = getArgs >>= mapM_ process
          
-- try with files ToHaskell/test/*.hascasl.hs
process :: FilePath -> IO () 
process fn = do
    s <- readFile fn
    let ts = pLexerPass0 True s
        Result ds m = do 
            HsModule _ _ _ _ b <- parseTokens HP.parse fn ts
            hatAna(HsDecls (preludeDecls ++ b), 
                                     emptySign, emptyGlobalAnnos) 
    case m of 
        Just (_, _, sig, hs) -> do
            putStrLn $ showPretty sig ""
            mapM_ (putStrLn . flip showPretty "") hs
        _ -> mapM_ (putStrLn . show) ds

