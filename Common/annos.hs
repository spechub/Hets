module Main where

import Common.Token
import Common.RunParsers
import Common.Anno_Parser
import Common.Lib.Pretty
import Common.PrettyPrint
import Common.GlobalAnnotationsFunctions
import Common.Print_AS_Annotation

main :: IO ()
main = exec lineParser fileParser

lineParser, fileParser :: [(String, StringParser)]
lineParser = [("MixIds", fromAParser parseId),
	      ("VarIds", fromAParser varId),
	      ("SortIds", fromAParser sortId),
	      ("Annos", fromAParser annotation)]

fileParser = [("Annotations", \ ga -> fmap (show . vcat . map 
					    (printText0 ga)) 
	       annotations)
	     ,("GlobalAnnos", \ ga -> fmap (show . addGlobalAnnos ga)
	       annotations)
	     ]


