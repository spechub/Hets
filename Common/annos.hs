{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable

test some parsers (and printers) for annotations
-}

module Main where

import Common.Token
import Common.RunParsers
import Common.Anno_Parser
import Common.Doc
import Common.DocUtils
import Common.AnalyseAnnos
import Common.Print_AS_Annotation()
import Common.ConvertGlobalAnnos()

main :: IO ()
main = exec lineParser fileParser

lineParser, fileParser :: [(String, StringParser)]
lineParser = [("MixIds", fromAParser $ parseId []),
              ("VarIds", fromAParser $ varId []),
              ("SortIds", fromAParser $ sortId []),
              ("Annos", fromAParser annotationL)]

fileParser = [("Annotations", \ ga -> fmap
               (show . useGlobalAnnos ga . vcat . map pretty)
               annotations)
             ,("GlobalAnnos", \ ga -> fmap
               (show . useGlobalAnnos ga . pretty . addGlobalAnnos ga)
               annotations)
             ]
