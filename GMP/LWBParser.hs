module Main where

import System.Environment
import Text.ParserCombinators.Parsec
import Lexer

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
prim =  do try(string "false")
           whiteSpace
           return "F"
    <|> do try(string "true")
           whiteSpace
           return "T"
    <|> do try(string "~")
           whiteSpace
           f <- lwb2sf
           return $ "~"++f
    <|> do try(string "box(")
           f <- lwb2sf
           char ')'
           return $ "[]"++f
    <|> do try(string "box")
           whiteSpace
           f <- prim
           return $ "[]"++f
    <|> do try (string "dia(")
           f <- lwb2sf
           char ')'
           return $ "<>"++f
    <|> do try (string "dia")
           whiteSpace
           f <- prim
           return $ "<>"++f
    <|> do try(string "p")
           i <- natural
           whiteSpace
           return $ "p" ++ show i
    <|> do try(char '(')
           f <- lwb2sf
           char ')'
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
               "./<exe> <path>\n" ++
               "<exe>  : executable file\n" ++
               "<path> : path to file to write into\n")
main :: IO()
main = do
    args <- getArgs
    if (args==[])||(head args == "--help")
      then help
      else do let p = head args
              putStrLn "Give the input formula:"
              line <- getLine
              runLex p lwb2sf line
