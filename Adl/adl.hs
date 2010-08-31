{-# LANGUAGE CPP #-}
{- |
Module      :  $Header$
Description :  ADL syntax parser
Copyright   :  (c) Stef Joosten, Christian Maeder DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable
-}

module Main (main) where

import Common.DocUtils (pretty)
import Common.Parsec ((<<))
import Common.Result
import Common.Lib.State
import Text.ParserCombinators.Parsec (parse, eof)

import Adl.As
import Adl.Parse (skip, pArchitecture)
import Adl.Sign
import Adl.StatAna

import Adl.Print
#ifdef LATEX
  (adlGA)
import Common.PrintLaTeX
import Common.Doc
#else
  ()
#endif

import System.Environment (getArgs)
import System.Exit (exitFailure)

main :: IO ()
main = getArgs >>= mapM_ process

process :: String -> IO ()
process f = do
  s <- readFile f
  case parse (skip >> pArchitecture << eof) f s of
    Right (Context m ps) ->
      let (nps, env) = runState (mapM anaPatElem ps) (toEnv emptySign)
          es = Context m nps
          ds = reverse $ msgs env
      in if null ds then
#ifdef LATEX
      putStrLn
      . renderLatex Nothing
      . toLatex adlGA
#else
      print
#endif
      $ pretty es
      else printDiags 5 ds >> exitFailure
    Left err -> fail $ show err
