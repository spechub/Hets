
-- provides a simple testing-tool for using ApplyXmlDiff upon a proper Xml-File

import Static.XSimplePath
import System.Environment

import Control.Monad
import qualified Control.Monad.Fail as Fail

import Text.XML.Light

main :: IO ()
main = do
  args <- getArgs
  case args of
    ("-p" : p1 : ps) -> printDiff p1 ps
    (p1 : ps) -> testDiff p1 ps
    _ -> putStrLn "missing arguments: xml-file location and diff/xupdate files"

printDiff :: FilePath -> [FilePath] -> IO ()
printDiff p1 ps = do
      xml <- readFile p1
      case parseXMLDoc xml of
        Just xml1 -> mapM_ (\ xup -> do
            diff <- readFile xup
            ef <- liftM snd $ changeXml xml1 diff
            print ef) ps
        _ -> Fail.fail "failed to parse xml-file"

testDiff :: FilePath -> [FilePath] -> IO ()
testDiff p1 ps = do
      xml <- readFile p1
      case parseXMLDoc xml of
        Just xml1 -> do
          xml2 <- foldM (\ xml' xup -> do
            diff <- readFile xup
            liftM fst $ changeXml xml' diff ) xml1 ps
          writeFile (p1 ++ "-output") $ ppTopElement xml2
        _ -> Fail.fail "failed to parse xml-file"
