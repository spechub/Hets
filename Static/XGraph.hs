{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./Static/XGraph.hs
Description :  xml input for Hets development graphs
Copyright   :  (c) Simon Ulbricht, DFKI GmbH 2011
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  tekknix@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (DevGraph)

convert an Xml-Graph into an XGraph-Structure.
-}

module Static.XGraph where

import Static.DgUtils

import Common.AnalyseAnnos (getGlobalAnnos)
import Common.Consistency (Conservativity (..))
import Common.GlobalAnnotations (GlobalAnnos, emptyGlobalAnnos)
import Common.LibName
import Common.Result (Result (..))
import Common.Utils (readMaybe)
import Common.XUpdate (getAttrVal, readAttrVal)

import Control.Monad
import qualified Control.Monad.Fail as Fail

import Data.Data
import Data.List
import Data.Maybe (fromMaybe)

import qualified Data.Set as Set
import qualified Data.Map as Map

import Text.XML.Light

{- -------------
Data Types -}

-- represent element information in the order they can be processed later
data XGraph = XGraph { libName :: LibName
                     , globAnnos :: GlobalAnnos
                     , nextLinkId :: EdgeId
                     , thmLinks :: [XLink]
                     , startNodes :: [XNode]
                     , xg_body :: XTree }
  deriving (Typeable, Data)

{- outer list must be executed in order; inner lists represent all def-links
-node bundles that can be processed in one step -}
type XTree = [[([XLink], XNode)]]

type EdgeMap = Map.Map String (Map.Map String [XLink])

data XNode = XNode { nodeName :: NodeName
                   , logicName :: String
                   , symbs :: (Bool, String) -- ^ hidden?
                   , specs :: String -- ^ Sentences
                   , nd_cons :: Conservativity }
           | XRef { nodeName :: NodeName
                  , refNode :: String
                  , refLib :: String
                  , specs :: String }
  deriving (Typeable, Data)

data XLink = XLink { source :: String
                   , target :: String
                   , edgeId :: EdgeId
                   , lType :: DGEdgeType
                   , rule :: DGRule
                   , cons :: Conservativity
                   , prBasis :: ProofBasis
                   , mr_name :: String
                   , mr_source :: Maybe String
                   , mapping :: String }
  deriving (Typeable, Data)

instance Show XNode where
  show xn = showName (nodeName xn)

instance Show XLink where
  show xl = showEdgeId (edgeId xl) ++ ": " ++ source xl ++ " -> " ++ target xl

instance Ord XLink where
  compare xl1 xl2 = compare (edgeId xl1, source xl1, target xl1)
    (edgeId xl2, source xl2, target xl2)

instance Eq XLink where
  a == b = compare a b == EQ

{- ------------
Functions -}

insertXLink :: XLink -> EdgeMap -> EdgeMap
insertXLink l = Map.insertWith (Map.unionWith (++)) (target l)
  $ Map.singleton (source l) [l]

mkEdgeMap :: [XLink] -> EdgeMap
mkEdgeMap = foldl (flip insertXLink) Map.empty

xGraph :: Element -> Result XGraph
xGraph xml = do
  allNodes <- extractXNodes xml
  allLinks <- extractXLinks xml
  _ <- foldM (\ s l -> let e = edgeId l in
    if Set.member e s then Fail.fail $ "duplicate edge id: " ++ show e
    else return $ Set.insert e s) Set.empty allLinks
  nodeMap <- foldM (\ m n -> let s = showName $ nodeName n in
    if Map.member s m then Fail.fail $ "duplicate node name: " ++ s
       else return $ Map.insert s n m) Map.empty allNodes
  let (thmLk, defLk) = partition (\ l -> case edgeTypeModInc $ lType l of
                         ThmType {} -> True
                         _ -> False) allLinks
      edgeMap = mkEdgeMap defLk
      (initN, restN) = Map.partitionWithKey
         (\ n _ -> Set.notMember n $ Map.keysSet edgeMap)
         nodeMap
      tgts = Map.keysSet nodeMap
      missingTgts = Set.difference (Map.keysSet edgeMap) tgts
      srcs = Set.unions $ map Map.keysSet $ Map.elems edgeMap
      missingSrcs = Set.difference srcs tgts
  unless (Set.null missingTgts)
    $ Fail.fail $ "missing nodes for edge targets " ++ show missingTgts
  unless (Set.null missingSrcs)
    $ Fail.fail $ "missing nodes for edge sources " ++ show missingSrcs
  nm <- getAttrVal "libname" xml
  fl <- getAttrVal "filename" xml
  let ln = setFilePath fl $ emptyLibName nm
  ga <- extractGlobalAnnos xml
  i' <- fmap readEdgeId $ getAttrVal "nextlinkid" xml
  xg <- builtXGraph (Map.keysSet initN) edgeMap restN []
  return $ XGraph ln ga i' thmLk (Map.elems initN) xg

builtXGraph :: Fail.MonadFail m => Set.Set String -> EdgeMap -> Map.Map String XNode
            -> XTree -> m XTree
builtXGraph ns xls xns xg = if Map.null xls && Map.null xns then return xg
  else do
  when (Map.null xls) $ Fail.fail $ "unprocessed nodes: " ++ show (Map.keysSet xns)
  when (Map.null xns) $ Fail.fail $ "unprocessed links: "
       ++ show (map edgeId $ concat $ concatMap Map.elems $ Map.elems xls)
  let (sls, rls) = Map.partition ((`Set.isSubsetOf` ns) . Map.keysSet) xls
      bs = Map.intersectionWith (,) sls xns
  when (Map.null bs) $ Fail.fail $ "cannot continue with source nodes:\n "
    ++ show (Set.difference (Set.unions $ map Map.keysSet $ Map.elems rls) ns)
    ++ "\nfor given nodes: " ++ show ns
  builtXGraph (Set.union ns $ Map.keysSet bs) rls
    (Map.difference xns bs) $
       map (\ (m, x) -> (concat $ Map.elems m, x)) (Map.elems bs) : xg

extractXNodes :: Fail.MonadFail m => Element -> m [XNode]
extractXNodes = mapM mkXNode . findChildren (unqual "DGNode")

extractXLinks :: Fail.MonadFail m => Element -> m [XLink]
extractXLinks = mapM mkXLink . findChildren (unqual "DGLink")

mkXNode :: Fail.MonadFail m => Element -> m XNode
mkXNode el = let spcs = unlines . map strContent
                   . concatMap (findChildren $ unqual "Text")
                   $ deepSearch ["Axiom", "Theorem"] el
                 get f s = f . map strContent . deepSearch [s]
                 get' = get unlines in do
  nm <- extractNodeName el
  case findChild (unqual "Reference") el of
    Just rf -> do
      rfNm <- getAttrVal "node" rf
      rfLib <- getAttrVal "library" rf
      return $ XRef nm rfNm rfLib spcs
    Nothing -> let
      hdSyms = case findChild (unqual "Hidden") el of
            Nothing -> case findChild (unqual "Declarations") el of
              -- Case #1: No declared or hidden symbols
              Nothing -> (False, "")
              -- Case #2: Node has declared symbols (DGBasicSpec)
              Just ch -> (False, get' "Symbol" ch)
            -- Case #3: Node has hidden symbols (DGRestricted)
            Just ch -> (True, get (intercalate ", ") "Symbol" ch)
      in do
        lgN <- getAttrVal "logic" el
        xp0 <- getAttrVal "relxpath" el
        nm0 <- getAttrVal "refname" el
        xp1 <- readXPath (nm0 ++ xp0)
        return $ XNode nm { xpath = reverse xp1 } lgN hdSyms spcs $ readCons el

extractNodeName :: Fail.MonadFail m => Element -> m NodeName
extractNodeName e = liftM parseNodeName $ getAttrVal "name" e

mkXLink :: Fail.MonadFail m => Element -> m XLink
mkXLink el = do
  sr <- getAttrVal "source" el
  tr <- getAttrVal "target" el
  ei <- extractEdgeId el
  tp <- case findChild (unqual "Type") el of
          Just tp' -> return $ revertDGEdgeTypeName $ strContent tp'
          Nothing -> Fail.fail "links type description is missing"
  rl <- case findChild (unqual "Rule") el of
          Nothing -> return $ DGRule "no rule"
          Just r' -> case findChildren (unqual "MovedTheorems") el of
            [] -> return $ DGRule $ strContent r'
            mThs -> liftM DGRuleLocalInference $ mapM (\ e -> do
                nmOld <- getAttrVal "name" e
                nmNew <- getAttrVal "renamedTo" e
                return (nmOld, nmNew)) mThs
  prB <- mapM (getAttrVal "linkref") $ findChildren (unqual "ProofBasis") el
  (mrNm, mrSrc) <- case findChild (unqual "GMorphism") el of
    Nothing -> Fail.fail "Links morphism description is missing!"
    Just mor -> do
        nm <- getAttrVal "name" mor
        return (nm, findAttr (unqual "morphismsource") mor)
  let parseSymbMap = intercalate ", " . map ( intercalate " |-> "
          . map strContent . elChildren ) . deepSearch ["map"]
      prBs = ProofBasis $ foldr (Set.insert . readEdgeId) Set.empty prB
      cc = readCons el
  return $ XLink sr tr ei tp rl cc prBs mrNm mrSrc $ parseSymbMap el

readCons :: Element -> Conservativity
readCons el = case findChild (unqual "ConsStatus") el of
  Nothing -> None
  Just c' -> fromMaybe None $ readMaybe $ strContent c'

extractEdgeId :: Fail.MonadFail m => Element -> m EdgeId
extractEdgeId = liftM EdgeId . readAttrVal "XGraph.extractEdgeId" "linkid"

readEdgeId :: String -> EdgeId
readEdgeId = EdgeId . fromMaybe (-1) . readMaybe

-- | custom xml-search for not only immediate children
deepSearch :: [String] -> Element -> [Element]
deepSearch tags e = filtr e ++ concatMap filtr (elChildren e) where
  filtr = filterChildrenName (`elem` map unqual tags)

-- | extracts the global annotations from the xml-graph
extractGlobalAnnos :: Element -> Result GlobalAnnos
extractGlobalAnnos dgEle = case findChild (unqual "Global") dgEle of
  Nothing -> return emptyGlobalAnnos
  Just gl -> parseAnnotations gl

parseAnnotations :: Element -> Result GlobalAnnos
parseAnnotations = getGlobalAnnos . unlines . map strContent
    . findChildren (unqual "Annotation")
