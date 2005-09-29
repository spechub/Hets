{- **********************************************************************

   $Source$

   $Date$
   $Revision$
   Author: Daniel Pratsch (Last modification by $Author$)

  ************************************************************************** 
-}

{-------------------------------------------------------
 testing file for CSP-CASL semantics
--------------------------------------------------------}
module Main where

import CspCASL.Parse_AS_CSP_CASL
import CspCASL.SignCSP
import CspCASL.StatAnaCSP
import CspCASL.AS_CSP_CASL

import Text.ParserCombinators.Parsec
import System.IO
import System.Environment

import Common.AnnoState
import Common.Result


--parseFile :: Show a => AParser a -> String -> IO ()
parseFile parser input filename
--        = case (runParser parser emptyAnnos "" input) of
        = case (runParser parser (emptyAnnos ()) "" input) of
            Left err -> do { putStr (filename ++ ": ")
                           ; putStr "parse error at "
                           ; print err
                           -- AMGQ: There must be a nicer way to print
                           -- a blank line than the following?
                           ; putStr "\n"
                           }
            Right x -> do let Result diags sig = statAna x
                          sequence $ map (putStrLn . show) diags 
                          print x                        
                          print sig

-- parseFiles: Given a list of filenames, parse each file in turn.

chosenParser :: AParser () C3PO
chosenParser = interim

parseFiles :: [String] -> IO()
parseFiles []                = do putStr ""           
parseFiles (filename:others) = do { input <- readFile filename
                                  ; parseFile chosenParser input filename
                                  ; parseFiles others
                                  }

-- printArgs: Test function for printing arguments - just mucking
-- around, really.

printArgs :: [String] -> IO()
printArgs [] = do putStr ""
printArgs (first:rest) = do {
                     ; print first
                     ; printArgs rest
                     }

-- Main: - calls parser for each file passed in.

main :: IO ()
main = do { filenames <- getArgs
          ; parseFiles filenames
--          ; fi les
--          ; c <- readFile (head les)
--          ; run cspCaslCSpec c
          }
