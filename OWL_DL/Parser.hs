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

propAndValidateNamespaces :: ResXmlTree
propAndValidateNamespaces t
      = checkErrs $ (propagateNamespaces 
                     {- .> validateNamespaces -} ) t

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
    fromXmlTrees = mapM fromXmlTree


instance XmlTransformer Ontology where
    fromXmlTree _ = Result{ diags = [],
			    maybeResult = (Nothing::Maybe Ontology)
		          }
{- 
   fromXmlTrees = Result{ diags = [],
			 maybeResult = Nothing
			}

-}
{-
owl_parserT :: String -> String -> Result XmlTree
owl_parserT fname fcont =
     Result ds mtree = checkErrs (tryP fname fcont)
     Result = propAndValidateNamespaces mtree
     canonicalizeAllNodes
     
owl_parser :: XmlTree -> Result Ontology
owl_parser = fromXmlTree 

-}

-- for test
tryP :: String -> String -> XmlTrees
tryP loc str = 
        parseXmlFromString (do x <- document; return [x]) loc str

