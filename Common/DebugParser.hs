{- |
Module      :  ./TPTP/Parse.hs
Description :  A Parser for the TPTP Syntax v6.4.0.11
Copyright   :  (c) Eugen Kuksa University of Magdeburg 2017
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Eugen Kuksa <kuksa@iks.cs.ovgu.de>
Stability   :  provisional
Portability :  portable

A Parser for the TPTP Input Syntax v6.4.0.11 taken from
<http://www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html>

References

[1] G. Sutcliffe et al.: The TPTP language grammar in BNF.
    <http://www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html>

    Note: The implemented version is saved at TPTP/Documents/SyntaxBNF.html

    Note: The names of the data types are aligned with the names of the
    grammar rules at this reference page (modulo case).
-}

module Common.DebugParser where

import Text.ParserCombinators.Parsec hiding (space)

import Debug.Trace
import Text.Printf

parserTraceId :: String -> CharParser st a -> CharParser st a
parserTraceId _ p = p

parserTraceLineNumber :: String -> CharParser st a -> CharParser st a
parserTraceLineNumber _ p = do
  s <- getParserState
  if 1 == (sourceColumn $ statePos s)
  then trace (show $ sourceLine $ statePos s) $ return ()
  else return ()
  p

parserTraceFull :: String -> CharParser st a -> CharParser st a
parserTraceFull msg p = do
  s <- getParserState
  if debug s
  then do
    let outBefore = takeWhile (\ c -> c /= '\n') $ take width (stateInput s)
    trace (parserMessage s outBefore) $ return ()
    parsed <- p
    s' <- getParserState
    let outAfter = takeConsumed outBefore s s'
    trace (successMessage s s' outBefore outAfter) $ return parsed
  else p
  where
    width = 54 :: Int
    space = 5 :: Int
    parserWidth = 24 :: Int
    parsedWidth = 24 :: Int
    debug _ = True -- 6 == (sourceLine $ statePos s)
    -- alternative (useful if parsing a specific line is broken - here: line 6):
    -- debug s = 6 == (sourceLine $ statePos s)
    line s = sourceLine $ statePos s
    column s = sourceColumn $ statePos s
    parserMessage s out =  printf ("%3d.%-4d - %" ++ show width ++ "s%" ++ show space ++ "s     %-" ++ show parserWidth ++ "s") (line s) (column s) out "" msg
    successMessage s s' outBefore outAfter = printf ("%3d.%-4d - %" ++ show width ++ "s%" ++ show space ++ "s --> %-" ++ show parserWidth ++ "s  =  %-"++ show parsedWidth ++"s  FROM  %3d.%-4d - %-s") (line s') (column s') "" "" msg outAfter (line s) (column s) outBefore
    takeConsumed :: String -> State s u -> State s u -> String
    takeConsumed outBefore stateBefore stateAfter =
      let consumedLength = sourceColumn (statePos stateAfter) - sourceColumn (statePos stateBefore)
      in take consumedLength outBefore
