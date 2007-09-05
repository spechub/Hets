module ToRacerParser where

import GMP.GMPParser
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
                               ;print err
                Right x ->  do writeFile path x
