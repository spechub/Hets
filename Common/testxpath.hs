import Common.XPath
import Text.ParserCombinators.Parsec
import Common.Parsec

main :: IO ()
main = do
  str <- getContents
  mapM_ process $ zip [1 .. ] $ lines str

process :: (Int, String) -> IO ()
process (n, str) = case parse (spaces >> expr << eof) "" str of
  Left err -> fail $ "line " ++ show n ++ ": " ++ show err
  Right e -> print e
