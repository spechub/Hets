module Main where

import GMP.GMPParser
import GMP.GradedML
import GMP.Lexer
import Text.ParserCombinators.Parsec
import System.Environment
import IO

{--
runLex :: (Ord a, Show a, ModalLogic a b) => String -> Parser (Formula a) -> String -> IO ()
runLex path p input = run (do
    whiteSpace
    ; x <- p
    ; eof
    ; return x
    ) input
--}
run :: (Ord a, Show a, ModalLogic a b) => String -> Parser (Formula a) -> String -> IO ()
run path p input
        = case (parse p "" input) of
                Left err -> do putStr "parse error at "
                               print err
                Right x ->  do return x
-- run ::
run path p f
        = case (parse p "" input) of
                Left err -> putStr "parse error at "
                            print err
                Right x -> do writeFile path (toString x)

help :: IO()
help = do
    putStrLn ("Usage:\n" ++
               "./<exe> <patho> <pathi>\n" ++
               "<exe>  : executable file\n" ++
               "<patho> : path to file to write into\n" ++
               "<pathi> : path to file to read from\n")
-- runGMP ::
runGMP p input = 
    run ( do whiteSpace
             x <- p
             eof
             return x ) input

runLex po f p =
    run 
main :: IO()
main = do
    args <- getArgs
    if (args==[])||(head args == "--help")||(length args < 2)
      then help
      else do let po = head args
                  pi = head (tail args)
              input <- readFile pi
              f <- runGMP ((par5er parseIndex) :: Parser (Formula GML)) input
              runLex po f toRparse
