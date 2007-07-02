module BParser where

import Text.ParserCombinators.Parsec
import Lexer
{-
lwbjunc :: Parser String
lwbjunc = do try(string
-}
-- parse lwb formulae as string and transform it to standard
lwb2sf :: Parser String
lwb2sf =  do try(string "False")
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
      <|> do try(string "&")
             whiteSpace
             return "/\\"
      <|> do try(string "v")
             whiteSpace
             return "\\/"
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
