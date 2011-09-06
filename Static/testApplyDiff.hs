
import Static.ApplyXmlDiff
import System.Environment
import Text.XML.Light (parseXMLDoc, showTopElement)

main :: IO()
main = do
  args <- getArgs
  case args of
    (p1 : p2 : _) -> testDiff p1 p2
    _ -> do
      putStrLn "please enter xml location!"
      p1 <- getLine
      putStrLn "please enter diff location!"
      p2 <- getLine
      testDiff p1 p2

testDiff :: FilePath -> FilePath -> IO()
testDiff p1 p2 = do
      xml <- readFile p1
      diff <- readFile p2
      case parseXMLDoc xml of
        Just xml1 -> do
          xml2 <- applyXmlDiff xml1 diff
          writeFile (p1 ++ "-output") $ showTopElement xml2
        _ -> fail "failed to parse xml-file"
