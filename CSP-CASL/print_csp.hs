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

import Parse_hugo
import Parsec
import IO
import System
import PrettyPrint
import Pretty
import Print_AS_CSP_CASL
import GlobalAnnotationsFunctions(emptyGlobalAnnos)

import AnnoState

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
