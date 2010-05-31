{- |
Module      :  $Header$
Description :  xml update input for Hets development graphs
Copyright   :  (c) Christian Maeder, DFKI GmbH 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

adjust development graph according to xupdate information
-}

module Static.FromXml where

import Static.DevGraph
import Static.GTheory
import Static.PrintDevGraph
import Static.ToXml

import Logic.Prover
import Logic.Logic
import Logic.Comorphism

import Common.AS_Annotation
import Common.ConvertGlobalAnnos
import Common.DocUtils
import Common.ExtSign
import Common.GlobalAnnotations
import Common.Id
import Common.LibName
import qualified Common.OrderedMap as OMap
import Common.Result
import Common.ToXml
import Common.XUpdate

import Text.XML.Light

import Data.Graph.Inductive.Graph as Graph
import qualified Data.Map as Map
import qualified Data.Set as Set

anaUpdates :: LibEnv -> DGraph -> String -> Result [Change]
anaUpdates _lenv _dg = anaXUpdates

-- | target data type of elements that may be added (via AddElem)
data AddChangeDG =
    SpecEntryDG
    { name :: SIMPLE_ID
    , formalParams :: Maybe NodeName
    }
  | ViewEntryDG
    { name :: SIMPLE_ID
    , formalParams :: Maybe NodeName
    , source :: NodeName
    , target :: NodeName
    , gmorphism :: String
    }
  | NodeDG -- no reference nodes yet
    { nName :: NodeName -- including xpath
    , refName :: Maybe SIMPLE_ID
    , consStatus :: String
    , declsOrSign :: DeclsOrSign
    }
  | LinkDG
    { linkId :: EdgeId
    , source :: NodeName
    , target :: NodeName
    , linkType :: String
    , gmorphism :: String
    }
  | GMorphismDG
    { gmorphism :: String }
  | SymbolDG
    { symbol :: String }
  | Affected
    { affected :: String }

data DeclsOrSign =
    DeclsDG
    { symbols :: [String] }
  | SignDG
    { sign :: String }

eName :: Element -> String
eName = qName . elName

-- | convert (parts of) an xupdate change (list) to more abstract change(s)
addChangeDG :: Monad m => AddChange -> m AddChangeDG
addChangeDG ac = case ac of
  AddElem e -> do
    n <- getNameAttr e
    case eName e of
      "SPEC_DEFN" ->
        return $ SpecEntryDG (mkSimpleId n) $ fmap parseNodeName
             $ getAttrVal "formal-param" e
      "DGNode" ->
        return $ NodeDG (parseNodeName n) -- getAttrVal "relxpath" e
           (fmap mkSimpleId $ getAttrVal "refname" e)
             undefined undefined
      en -> fail $ "Static.FromXML.addChangeDG: unexpected element: " ++ en
  _ -> fail "Static.FromXML.addChangeDG: unexpected added change"
