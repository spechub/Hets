
-- provides a simple testing-tool for using ApplyXmlDiff upon a proper Xml-File

import Static.ApplyXmlDiff
import System.Environment
import Control.Monad (foldM)
import Text.XML.Light

main :: IO()
main = do
  args <- getArgs
  case args of
    ("-p" : p1 : ps) -> printDiff p1 ps
    (p1 : ps) -> testDiff p1 ps
    _ -> putStrLn "missing arguments: xml-file location and diff/xupdate files"

printDiff :: FilePath -> [FilePath] -> IO()
printDiff p1 ps = do
      xml <- readFile p1
      case parseXMLDoc xml of
        Just xml1 -> mapM_ (\ xup -> do
            diff <- readFile xup
            printXmlDiff xml1 diff ) ps
        _ -> fail "failed to parse xml-file"

testDiff :: FilePath -> [FilePath] -> IO()
testDiff p1 ps = do
      xml <- readFile p1
      case parseXMLDoc xml of
        Just xml1 -> do
          xml2 <- foldM (\ xml' xup -> do
            diff <- readFile xup
            applyXmlDiff xml' diff ) xml1 ps
          writeFile (p1 ++ "-output") $ ppTopElement xml2
        _ -> fail "failed to parse xml-file"
