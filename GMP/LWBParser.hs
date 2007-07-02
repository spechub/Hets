module LWBParser where

import Text.ParserCombinators.Parsec
import Lexer

lwbjunc :: Parser String
lwbjunc =  do try(string "&"); return "/\\"
       <|> do try(string "v"); return "\\/"
       <|> do try(string "->"); return "->"
       <|> do try(string "<->"); return "<->"

lwb2sf :: Parser String
lwb2sf = do f <- prim; option (f) (inf f)

inf :: String -> Parser String
inf f = do iot <- lwbjunc; ff <- lwb2sf; return $ "("++f++iot++ff++")"

prim :: Parser String
prim =  do try(string "False")
           whiteSpace
           return "F"
    <|> do try(string "True")
           whiteSpace
           return "T"
    <|> do try(string "~")
           whiteSpace
           return "~"
    <|> do try(string "box")
           whiteSpace
           return "[]"
    <|> do try (string "dia")
           whiteSpace
           return "<>"
    <|> do try(char '(')
           whiteSpace
           f <- lwb2sf
           char ')'
           whiteSpace
           return f
    <|> do try(string "p")
           i <- natural
           return $ "p" ++ show i

run :: Show a => Parser a -> String -> IO ()
run p input
        = case (parse p "" input) of
            Left err -> do putStr "parse error at "
                           print err
            Right x  -> print x


runLex :: Show a => Parser a -> String -> IO ()
runLex p
        = run (do whiteSpace
                  x <- p
                  eof
                  return x
              )
