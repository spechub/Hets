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

import System.Environment
import Text.ParserCombinators.Parsec
import GMP.Lexer

lwbjunc :: Parser String
lwbjunc =  do try(string "&");   whiteSpace; return "/\\"
       <|> do try(string "v");   whiteSpace; return "\\/"
       <|> do try(string "->");  whiteSpace; return "->"
       <|> do try(string "<->"); whiteSpace; return "<->"

lwb2sf :: Parser String
lwb2sf = do f <- prim; option (f) (inf f)

inf :: String -> Parser String
inf f = do iot <- lwbjunc; ff <- lwb2sf; return $ "("++f++iot++ff++")"

prim :: Parser String
prim =  do whiteSpace
           try(string "false")
           whiteSpace
           return "F"
    <|> do whiteSpace
           try(string "true")
           whiteSpace
           return "T"
    <|> do whiteSpace
           try(string "~")
           whiteSpace
           f <- lwb2sf
           whiteSpace
           return $ "~"++f
    <|> do whiteSpace
           try(string "box(")
           whiteSpace
           f <- lwb2sf
           whiteSpace
           char ')'
           whiteSpace
           return $ "[]"++f
    <|> do whiteSpace
           try(string "box")
           whiteSpace
           f <- prim
           whiteSpace
           return $ "[]"++f
    <|> do whiteSpace
           try(string "dia(")
           whiteSpace
           f <- lwb2sf
           whiteSpace
           char ')'
           whiteSpace
           return $ "<>"++f
    <|> do whiteSpace
           try(string "dia")
           whiteSpace
           f <- prim
           whiteSpace
           return $ "<>"++f
    <|> do whiteSpace
           try(string "p")
           i <- natural
           whiteSpace
           return $ "p" ++ show i
    <|> do whiteSpace
           try(char '(')
           whiteSpace
           f <- lwb2sf
           whiteSpace
           char ')'
           whiteSpace
           return f
    <|> do whiteSpace
           f <- lwb2sf
           whiteSpace
           return f
    <?> "prim"

run :: String -> Parser String -> String -> IO ()
run path p input
        = case (parse p "" input) of
            Left err -> do putStr "parse error at "
                           print err
            Right x  -> writeFile path x


runLex :: String -> Parser String -> String -> IO ()
runLex path p
        = run path (do whiteSpace
                       x <- p
                       eof
                       return x)

help :: IO()
help = do
    putStrLn ("Usage:\n" ++
               "\t./<exe> <patho> <pathi>\n" ++
               "<exe>   : executable file\n" ++
               "<patho> : path to file to write into\n" ++
               "<pathi> : path to file to read from\n")
main :: IO()
main = do
    args <- getArgs
    if (args==[])||(head args == "--help")||(length args < 2)
      then help
      else do let fo = head args
                  fi = head (tail args)
              line <- readFile fi
              runLex fo lwb2sf line
