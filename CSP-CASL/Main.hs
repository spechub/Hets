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

import AnnoState

run :: Show a => AParser a -> String -> IO ()
run p input
        = case (runParser p emptyAnnos "" input) of
            Left err -> do { putStr "parse error at "
                           ; print err
                           }
            Right x -> print x                        

main :: IO ()
main = do { l <- getArgs
          ; c <- readFile (head l)
          ; run cspCaslCSpec c
          }
