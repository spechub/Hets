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

import CspCASL.Parse_hugo
import Common.Lib.Parsec
import System.IO
import System.Environment
import Common.PrettyPrint
import Common.Lib.Pretty
import CspCASL.Print_AS_CSP_CASL
import Common.GlobalAnnotationsFunctions(emptyGlobalAnnos)

import Common.AnnoState

run :: PrettyPrint a => AParser a -> String -> IO ()
run p input
        = case (runParser p emptyAnnos "" input) of
            Left err -> do { putStr "parse error at "
                           ; print err
                           }
            Right x -> putStrLn $ renderText Nothing $
		       printText0 emptyGlobalAnnos x                        

main :: IO ()
main = do { l <- getArgs
          ; c <- readFile (head l)
          ; run cspCaslCSpec c
          }
