module Main where

import Common.Token
import Common.RunParsers
import Common.Anno_Parser
import Common.Lib.Pretty
import Common.PrettyPrint
import Common.AnalyseAnnos
import Common.Print_AS_Annotation
import Common.ConvertGlobalAnnos

main :: IO ()
main = exec lineParser fileParser

lineParser, fileParser :: [(String, StringParser)]
lineParser = [("MixIds", fromAParser $ parseId []),
              ("VarIds", fromAParser $ varId []),
              ("SortIds", fromAParser $ sortId []),
              ("Annos", fromAParser annotationL)]

fileParser = [("Annotations", \ ga -> fmap (show . vcat . map 
                                            (printText0 ga)) 
               annotations)
             ,("GlobalAnnos", \ ga -> fmap 
               (show . printText0 ga . addGlobalAnnos ga)
               annotations)
             ]


