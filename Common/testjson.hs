import Common.Json
import Common.Parsec
import Text.ParserCombinators.Parsec

main = do
  str <- getContents
  case parse (spaces >> pJson << eof) "" str of
    Right e -> putStr $ ppJson e
    Left e -> print e
