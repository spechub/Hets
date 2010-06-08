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
import Common.XPath
import Common.XUpdate

import Text.XML.Light

import Data.Graph.Inductive.Graph as Graph
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List
import Data.Maybe
import Control.Monad

anaUpdates = do
  input <- readFile "Common/test/diff.AddingImports.decomposed.xml"
  cs <- anaXUpdates input
  acs <- mapM changeDG cs
  mapM_ print acs

-- | target data type of elements that may be added (via AddElem)
data AddChangeDG
  = SpecEntryDG
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
  | SymbolDG String
  | Affected
    { affected :: String }
  deriving Show

data DeclsOrSign
  = DeclsDG
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
  AddElem e -> case eName e of
      "SPEC-DEFN" -> do
        n <- getNameAttr e
        return SpecEntryDG
          { name = mkSimpleId n
          , formalParams = fmap parseNodeName $ getAttrVal "formal-param" e
          }
      "DGNode" -> do
        n <- getNameAttr e
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
      "Symbol" -> return $ SymbolDG $ strContent e
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

changeDG :: Monad m => Change -> m (SelElems, [AddChangeDG])
changeDG (Change csel path) = do
  se <- anaTopPath path
  cs <- case csel of
    Add _ cs -> mapM addChangeDG cs
    Remove -> return []
    Update _ -> return []
    _ -> fail "Static.FromXML.changeDG: unexpected change"
  return (se, cs)

data NodeSubElem
  = AttributeName String
  | DeclSymbol
  | SymbolRangeAttr Int
    deriving Show

data ViewDefnElem = RangeAttr | ViewMorphism deriving Show

data LinkSubElem = LinkMorphism deriving Show

data SelElems
  = NodeElem NodeName (Maybe NodeSubElem)
  | SpecDefn SIMPLE_ID (Maybe String) -- attribute
  | ViewDefn SIMPLE_ID (Maybe ViewDefnElem)
  | LinkElem EdgeId NodeName NodeName (Maybe LinkSubElem)
    deriving Show

anaTopPath :: Monad m => Expr -> m SelElems
anaTopPath e = case e of
  PathExpr Nothing (Path True (stp : stps)) -> do
    unless (checkStepElement "DGraph" stp)
      $ fail $ "Static.FromXML.checkStepElement: "
       ++ "\n found: " ++ showStep stp
    anaSteps stps
  _ -> fail $ "Static.FromXML.anaTopPath: " ++ showExpr e

checkStepElement :: String -> Step -> Bool
checkStepElement str stp = case stp of
  Step Child (NameTest l) _ | l == str -> True
  _ -> False

anaSteps :: Monad m => [Step] -> m SelElems
anaSteps stps = case stps of
   Step Child (NameTest l) ps : rst -> case l of
     "DGNode" -> do
       nn <- liftM parseNodeName $ getStepNameAttr ps
       nse <- getNodeSubElem rst
       return $ NodeElem nn nse
     "SPEC-DEFN" -> do
       n <- getStepNameAttr ps
--       unless (null rst) $ fail
--         $ "Static.FromXML.anaSteps: unexpected steps after: " ++ l
--         ++ "\n" ++ showSteps False rst
       return $ SpecDefn (mkSimpleId n) Nothing -- ignore range attribute
     "VIEW-DEFN" -> do
       n <- getStepNameAttr ps
--       unless (null rst) $ fail
--         $ "Static.FromXML.anaSteps: unexpected steps after: " ++ l
--         ++ "\n" ++ showSteps False rst
       return $ ViewDefn (mkSimpleId n) Nothing -- ignore range attribute
     "DGLink" -> do
       let as = getStepAttrs ps
       lnkId <- findAttrKey "linkid" as
       edgeId <- maybe (fail $ "Static.FromXML.anaSteps.edgeId: " ++ lnkId)
          return $ readMaybe lnkId
       s <- findAttrKey "source" as
       t <- findAttrKey "target" as
--       unless (null rst) $ fail
--         $ "Static.FromXML.anaSteps: unexpected steps after: " ++ l
--         ++ "\n" ++ showSteps False rst
       return $ LinkElem (EdgeId edgeId) (parseNodeName s) (parseNodeName t)
         Nothing
     _ -> fail $ "Static.FromXML.anaSteps: unexpected name: " ++ l
   [] -> fail "Static.FromXML.anaSteps: missing step"
   stp : _ ->
       fail $ "Static.FromXML.anaSteps: unexpected step: " ++ showStep stp

findAttrKey :: Monad m => String -> [Attr] -> m String
findAttrKey k = maybe (fail $ "findAttrKey: " ++ k)
 (maybe (fail "readAttrString") return . readMaybe . attrVal)
 . find ((== k) . qName . attrKey)

getStepNameAttr :: Monad m => [Expr] -> m String
getStepNameAttr = findAttrKey "name" . getStepAttrs

getStepAttrs :: [Expr] -> [Attr]
getStepAttrs = concatMap getExprAttrs

getExprAttrs :: Expr -> [Attr]
getExprAttrs = map (uncurry mkAttr) . mapMaybe lookupAttrEq . getConjuncts

getConjuncts :: Expr -> [Expr]
getConjuncts e = case e of
  GenExpr True "and" es -> concatMap getConjuncts es
  _ -> [e]

lookupAttrEq :: Expr -> Maybe (String, String)
lookupAttrEq e = case e of
  GenExpr True "=" [e1, e2] ->
    liftM2 (,) (getAttrExpr e1) $ getLitExpr e2
  _ -> Nothing

getLitExpr :: Expr -> Maybe String
getLitExpr e = case e of
  PrimExpr Literal str -> Just str
  _ -> Nothing

getAttrExpr :: Expr -> Maybe String
getAttrExpr e = case e of
  PathExpr Nothing (Path False [Step Attribute (NameTest s) []]) -> Just s
  _ -> Nothing

getNodeSubElem :: Monad m => [Step] -> m (Maybe NodeSubElem)
getNodeSubElem _ = return Nothing
