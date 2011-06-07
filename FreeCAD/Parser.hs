module FreeCAD.Parser
    where

import FreeCAD.Translator
import Data.Maybe
import Text.XML.Light.Input
import System.Directory
import System.Process
import FreeCAD.PrintAs


--the IO part of the program:--
-- processFile "FreeCAD/input.xml"
processFile :: FilePath -> IO ()
processFile fp = do
  tempDir <- getTemporaryDirectory
--  putStrLn $ show $ ["unzip", "-of", fp, "-d", tempDir]
  readProcess "unzip" ["-o", fp, "-d", tempDir] []
  xmlInput <-readFile (concat[tempDir, "/Document.xml"])
  let parsed = parseXMLDoc xmlInput
  out <- translate (fromJust parsed)
  putStrLn (show $printDoc out)
------------------------


