{-# LANGUAGE CPP #-}
{- |
Module      :  $Header$
Description :  ADL syntax parser
Copyright   :  (c) Stef Joosten, Christian Maeder DFKI GmbH 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable
-}

import Common.DocUtils (pretty)
import Common.Parsec ((<<))
import System.Environment (getArgs)
import Text.ParserCombinators.Parsec (parse, eof)

import Adl.Parse (skip, pArchitecture)
import Adl.Print
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
    Right es ->
#ifdef LATEX
      putStrLn
      . renderLatex Nothing
      . toLatex adlGA
#else
      print
#endif
      $ pretty es
    Left err -> fail $ show err
