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

import Common.AnnoState

run :: Show a => AParser a -> String -> IO ()
run p input
        = case (runParser p emptyAnnos "" input) of
            Left err -> do { putStr "parse error at "
                           ; print err
                           }
            Right x -> print x                        

fi :: [String] -> IO()
fi (l:es) = do { c <- readFile l
               ; run interim c
               ; fi es
               }
fi []     = do putStr ""           

main :: IO ()
main = do { les <- getArgs
          ; fi les
--          ; c <- readFile (head les)
--          ; run cspCaslCSpec c
          }
