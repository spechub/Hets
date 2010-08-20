{-# LANGUAGE CPP #-}
{- |
Module      :  $Header$
Description :  ADL syntax parser
Copyright   :  (c) Stef Joosten, Christian Maeder DFKI GmbH 2010
License     :  GPLv2 or higher

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable
-}

module Main (main) where

import Common.DocUtils (pretty)
import Common.Parsec ((<<))
import System.Environment (getArgs)
import Text.ParserCombinators.Parsec (parse, eof)

import Adl.Parse (skip, pArchitecture)
import Adl.Print
import Adl.Sign
import Adl.StatAna
#ifdef LATEX
  (adlGA)
import Common.PrintLaTeX
import Common.Doc
#else
  ()
#endif

main :: IO ()
main = getArgs >>= mapM_ process

process :: String -> IO ()
process f = do
  s <- readFile f
  case parse (skip >> pArchitecture << eof) f s of
    Right (Context m ps) ->
      let (nps, env) = runState (mapM anaPatElem ps) (toEnv emptySign)
          es = Context m nps
      in
#ifdef LATEX
      putStrLn
      . renderLatex Nothing
      . toLatex adlGA
#else
      print
#endif
      $ pretty es
    Left err -> fail $ show err
