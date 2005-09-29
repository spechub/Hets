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
import Text.ParserCombinators.Parsec
import System.IO
import System.Environment
import Common.PrettyPrint
import Common.Lib.Pretty
import CspCASL.Print_AS_CSP_CASL
import Common.GlobalAnnotations

import Common.AnnoState

run :: PrettyPrint a => AParser () a -> String -> IO ()
run p input
        = case (runParser p (emptyAnnos ()) "" input) of
            Left err -> do { putStr "parse error at "
                           ; print err
                           }
            Right x -> putStrLn $ renderText Nothing $
                       printText0 emptyGlobalAnnos x                        

main :: IO ()
main = do { l <- getArgs
          ; c <- readFile (head l)
          ; run interim c
          }
