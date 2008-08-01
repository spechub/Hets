{- |
Module      :  $Id$
Description :  a test driver for Haskell analysis
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  non-portable

test the programatica parser and (HatAna) analysis
-}

module Main where

import Haskell.HatParser
import Haskell.HatAna
import ParseMonad
import PropLexer
import PropParser as HP
import PropPosSyntax

import System.Environment

import Common.Result
import Common.GlobalAnnotations
import Common.DocUtils
import Common.AS_Annotation

main :: IO ()
main = getArgs >>= mapM_ process

-- try with files ToHaskell/test/*.hascasl.hs
process :: FilePath -> IO ()
process fn = do
    s <- readFile fn
    let ts = pLexerPass0 True s
        Result ds m = do
            HsModule _ _ _ _ b <- parseTokens HP.parse fn ts
            hatAna(HsDecls b, emptySign, emptyGlobalAnnos)
    case m of
        Just (_, sig, hs) -> do
            putStrLn $ showDoc sig ""
            mapM_ (putStrLn . flip showDoc "" . sentence) hs
        _ -> mapM_ (putStrLn . show) ds
