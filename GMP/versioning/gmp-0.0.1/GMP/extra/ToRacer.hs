{- |
Module      :  $EmptyHeader$
Description :  <optional short description entry>
Copyright   :  (c) <Authors or Affiliations>
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  <email>
Stability   :  unstable | experimental | provisional | stable | frozen
Portability :  portable | non-portable (<reason>)

<optional description>
-}
module Main where

import Text.ParserCombinators.Parsec
import System.Environment
import IO

import GMP.GMPAS
import GMP.GMPParser
import GMP.Lexer

import GMP.ModalLogic
import GMP.GradedML

runLex :: Parser (Formula GML) -> String -> FilePath -> IO ()
runLex p input path
    = run (do whiteSpace
              x <- p
              eof
              return x) input path

run :: Parser (Formula GML) -> String -> FilePath -> IO ()
run p input path
    = case (parse p "" input) of
        Left err -> do putStr "parse error at "
                       print err
        Right x ->  do let rFormula = "(concept-subsumes? " ++ toRF x ++
                                      "(or a (not a))" ++ ")"
                       writeFile (path++".racer") rFormula

--toRF
toRF f =
 case f of
   T               -> "(or c (not c))"
   F               -> "(and c (not c))"
   Neg g           -> "(not " ++ toRF g ++ ")"
   Junctor g Or h  -> "(or " ++ toRF g ++ " " ++ toRF h ++ ")"
   Junctor g And h -> "(and " ++ toRF g ++ " " ++ toRF h ++ ")"
   Junctor g If h  -> "(or " ++ toRF (Neg g) ++ " " ++ toRF h ++ ")"
   Junctor g Fi h  -> "(or " ++ toRF g ++ " " ++ toRF (Neg h) ++ ")"
   Junctor g Iff h -> "(and " ++ toRF (Junctor g If h) ++ " " ++
                                 toRF (Junctor g Fi h) ++ ")"
   Mapp (Mop (GML i) Angle) g
                   -> "(at-least " ++ show (i+1) ++ " R " ++ toRF g ++ ")"
   Mapp (Mop (GML i) Square) g
                   -> "(at-most " ++ show i ++ " R " ++ toRF (Neg g) ++ ")"
   Var c x         -> case x of
                        Nothing -> [c]
                        Just i  -> [c] ++ show i

runTest :: FilePath -> FilePath -> IO ()
runTest ipath opath
    = do input <- readFile (ipath)
         runLex ((par5er parseIndex) :: Parser (Formula GML)) input opath
         return ()

help :: IO()
help = do
    putStrLn ( "Usage:\n" ++
               "    ./<exe> <input> <output>\n\n" ++
               "<exe>:     the executable file\n" ++
               "<input>:   path to the input file\n" ++
               "<output>:  path to the output file\n" )

main :: IO()
main = do
    args <- getArgs
    if (args == [])||(head args == "--help")||(length args < 2)
     then help
     else let ipath = head args
              opath = head (tail args)
          in runTest ipath opath
