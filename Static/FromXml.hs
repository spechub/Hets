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
import Common.Utils
import Common.XUpdate

import Text.XML.Light

import Data.Graph.Inductive.Graph as Graph
import qualified Data.Map as Map
import qualified Data.Set as Set

anaUpdates :: LibEnv -> DGraph -> String -> Result [AddChangeDG]
anaUpdates _lenv _dg input = do
  cs <- anaXUpdates input
  acs <- mapM changeDG cs
  return $ concat acs

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
  deriving Show

data DeclsOrSign =
    DeclsDG
    { symbols :: [String] }
  | SignDG
    { sign :: String }
  deriving Show

eName :: Element -> String
eName = qName . elName

findChildrenByLocalName :: String -> Element -> [Element]
findChildrenByLocalName str = filterChildrenName ((== str) . qName)

getElementTexts :: String -> Element -> [String]
getElementTexts str = map strContent . findChildrenByLocalName str

-- | convert (parts of) an xupdate change (list) to more abstract change(s)
addChangeDG :: Monad m => AddChange -> m AddChangeDG
addChangeDG ac = case ac of
  AddElem e -> do
    n <- getNameAttr e
    case eName e of
      "SPEC_DEFN" ->
        return SpecEntryDG
          { name = mkSimpleId n
          , formalParams = fmap parseNodeName $ getAttrVal "formal-param" e
          }
      "DGNode" -> do
        dOrS <- getDeclsOrSign e
        return NodeDG
          { nName = parseNodeName n -- getAttrVal "relxpath" e
          , refName = fmap mkSimpleId $ getAttrVal "refname" e
          , consStatus = concat $ getElementTexts "ConsStatus" e
          , declsOrSign = dOrS
          }
      "DGLink" -> do
        lnkId <- getAttrVal "linkid" e
        edgeId <- maybe (fail "Static.FromXML.addChangeDG.DGLink.edgeId")
          return $ readMaybe lnkId
        src <- getAttrVal "source" e
        tar <- getAttrVal "target" e
        gmor <- getGMorphism e
        return LinkDG
          { linkId = EdgeId edgeId
          , source = parseNodeName src
          , target = parseNodeName tar
          , linkType = concat $ getElementTexts "Type" e
          , gmorphism = gmor
          }
      "GMorphism" -> return GMorphismDG
         { gmorphism = strContent e }
      "Symbol" -> return SymbolDG
         { symbol = strContent e }
      en -> fail $ "Static.FromXML.addChangeDG: unexpected element: " ++ en
  AddAttr a -> return Affected
      { affected = qName $ attrKey a }
  _ -> fail "Static.FromXML.addChangeDG: unexpected added change"

getGMorphism :: Monad m => Element -> m String
getGMorphism e = case getElementTexts "GMorphism" e of
  [ s ] -> return s
  _ -> fail "Static.FromXML.getGMorphism"

getDeclsOrSign :: Monad m => Element -> m DeclsOrSign
getDeclsOrSign e = case findChildrenByLocalName "Declarations" e of
  [ d ] -> return DeclsDG { symbols = getElementTexts "Symbol" d }
  _ -> case getElementTexts "Signature" e of
    [ str@(_ : _) ] -> return SignDG { sign = str }
    _ -> fail "Static.FromXML.getDeclsOrSign"

changeDG :: Monad m => Change -> m [AddChangeDG]
changeDG (Change sel _) = case sel of
   Add _ cs -> mapM addChangeDG cs
   _ -> fail "Static.FromXML.addChangeDG: unexpected change"
