{- |
Module      :  $Header$
Copyright   :  (c) Heng Jiang, Uni Bremen 2004-2005
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   Here is the place where the class Logic is instantiated for CASL.
   Also the instances for Syntax an Category.
-}

module OWL_DL.Parser where

import OWL_DL.AS
import Text.XML.HXT.DOM.XmlTree
import Text.XML.HXT.DOM.XmlTreeTypes
import Text.XML.HXT.DOM.XmlKeywords
import Text.XML.HXT.DOM.Namespace
import Text.XML.HXT.DOM.EditFilters
import Text.XML.HXT.DOM.FormatXmlTree
import Text.XML.HXT.Parser.XmlParser
import Common.Result
import Common.Id

type ResXmlTree = XmlTree -> Result XmlTrees
type ResXmlTrees = XmlTrees -> Result XmlTrees

propAndValideNamespaces :: ResXmlTree
propAndValideNamespaces t
      = checkErrs $ (propagateNamespaces 
                     .> validateNamespaces 
                     .> canonicalizeAllNodes) t

checkErrs :: ResXmlTrees
checkErrs [] = Result { diags = [], maybeResult = Just []}
checkErrs xt@[(NTree node ntrees)] = 
       case node of
       XError n diag -> 
           let kind = case n of
                             1 -> Warning
                             2 -> Error
                             3 -> Error
                             _ -> Hint
               diagnosis = Diag{ diagKind = kind,
                                 diagString  = diag,
                                 diagPos      = nullPos
                               }
           in  Result{ diags = [diagnosis],
                       maybeResult = Nothing
                     }
       _  -> Result{ diags = [],
                     maybeResult = Just xt
                   }


class XmlTransformer a where
    fromXmlTree  :: XmlTree  -> Result a
    fromXmlTrees :: XmlTrees -> Result [a]


{-
instance XmlTransformer Ontology where
   fromXmlTree = Result{ diags = [],
			 maybeResult = Nothing
		       }
 
   fromXmlTrees = Result{ diags = [],
			 maybeResult = Nothing
			}

-}



-- for test
tryP :: String -> String -> XmlTrees
tryP loc str = 
        parseXmlFromString (do x <- document; return [x]) loc str

