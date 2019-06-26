module FreeCAD.Main where

import FreeCAD.Translator
import FreeCAD.HetPrinter
import FreeCAD.As
import System.FilePath
import Common.Lib.Pretty

main :: IO ()

main = do
  doc <- processFile "./FreeCAD/test.fcstd"
  writeFile "./FreeCAD/test.dol" $ show $ printDoc "nametest" doc
