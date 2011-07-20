{- |
Module      :  $Header$
Description :  xml input for Hets development graphs
Copyright   :  (c) Simon Ulbricht, DFKI GmbH 2011
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  tekknix@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (DevGraph)

convert an Xml-Graph into an XGraph-Structure.
-}

module Static.XGraph where

import Static.DevGraph

import Common.Consistency (Conservativity (..))
import Common.Utils (readMaybe)
import Common.XUpdate (getAttrVal)

import Data.List (partition, intercalate)
import Data.Maybe (fromMaybe)

import qualified Data.Set as Set (empty, insert)

import Text.XML.Light

{- -------------
Data Types -}

{- the XGraph data structure contains the elements in exactly the opposite
order that they can be reconstructed later.
 - Top element holds all Theorem Links and the remaining Graph.
 - Branch holds a list of Definition Links and their Target-Node
 - Root contains all independent Nodes -}
data XGraph = Top [XLink] XGraph
            | Branch XNode [XLink] XGraph
            | Root [XNode]


data XNode = XNode { name :: String
                   , logicName :: String
                   , symbs :: (Bool, String) -- ^ hidden?
                   , specs :: String } -- ^ Sentences
           | XRef { name :: String
                  , refNode :: String
                  , refLib :: String
                  , specs :: String }

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

{- ------------
Functions -}

xGraph :: Monad m => Element -> m XGraph
xGraph xml = do
  allNodes <- extractXNodes xml
  allLinks <- extractXLinks xml
  let (thmLk, defLk) = partition (\ l -> case edgeTypeModInc $ lType l of
                         ThmType _ _ _ _ -> True
                         _ -> False ) allLinks
  (initN, restN) <- case partition
     (\ n -> not $ elem (name n) $ map target defLk) allNodes of
       ([], _) -> fail "found no independent nodes to start DGraph with"
       l -> return l
  xg <- builtXGraph defLk restN $ Root initN
  return $ Top thmLk xg 

builtXGraph :: Monad m => [XLink] -> [XNode] -> XGraph -> m XGraph
builtXGraph [] [] xg = return xg
builtXGraph [] _ _ = fail "builtXGraph: unexpected error (1)"
builtXGraph _ [] _ = fail "builtXGraph: unexpected error (2)"
builtXGraph ls (nd : nR) xg = let
  (lCur, lRest) = partition ((== name nd) . target) ls
  in if any (`elem` (map name nR)) $ map source lCur
        then builtXGraph ls (nR ++ [nd]) xg
        else builtXGraph lRest nR $ Branch nd lCur xg

extractXNodes :: Monad m => Element -> m [XNode]
extractXNodes = mapM mkXNode . findChildren (unqual "DGNode")

extractXLinks :: Monad m => Element -> m [XLink]
extractXLinks = mapM mkXLink . findChildren (unqual "DGLink")

mkXNode :: Monad m => Element -> m XNode
mkXNode el = let get f s = f . map strContent . findChildren (unqual s)
                 get' s = get unlines s in do
  nm <- getAttrVal "name" el
  case findChild (unqual "Reference") el of
    Just rf -> do
      rfNm <- getAttrVal "node" rf
      rfLib <- getAttrVal "library" rf
      return $ XRef nm rfNm rfLib $ get' "Axiom" el ++ get' "Theorem" el
    Nothing -> let
      hdSyms = case findChild (unqual "Hidden") el of
            Nothing -> case findChild (unqual "Declarations") el of
              -- Case #1: No declared or hidden symbols
              Nothing -> (False, "")
              -- Case #2: Node has declared symbols (DGBasicSpec)
              Just ch -> (False, get' "Symbol" ch)
            -- Case #3: Node has hidden symbols (DGRestricted)
            Just ch -> (True, get (intercalate ", ") "Symbol" ch)
      spcs = get' "Axiom" el ++ get' "Theorem" el
      in do
        lg <- getAttrVal "logic" el
        return $ XNode nm lg hdSyms spcs

mkXLink :: Monad m => Element -> m XLink
mkXLink el = do
  sr <- getAttrVal "source" el
  tr <- getAttrVal "target" el
  ei <- getAttrVal "linkid" el
  tp <- case findChild (unqual "Type") el of
          Just tp' -> return $ revertDGEdgeTypeName $ strContent tp'
          Nothing -> fail "links type description is missing"
  let rl = case findChild (unqual "Rule") el of
            Nothing -> "no rule"
            Just r' -> strContent r'
      cc = case findChild (unqual "ConsStatus") el of
            Nothing -> None
            Just c' -> fromMaybe None $ readMaybe $ strContent c'
  prB <- mapM (getAttrVal "linkref") $ findChildren (unqual "ProofBasis") el
  (mrNm, mrSrc) <- case findChild (unqual "GMorphism") el of
    Nothing -> fail "Links morphism description is missing!"
    Just mor -> do
        nm <- getAttrVal "name" mor
        return (nm, findAttr (unqual "morphismsource") mor)
  let parseSymbMap = intercalate ", " . map ( intercalate " |-> "
          . map strContent . elChildren ) . deepSearch ["map"]
      ei' = readEdgeId ei
      prBs = ProofBasis $ foldr Set.insert Set.empty $ map readEdgeId prB
  return $ XLink sr tr ei' tp (DGRule rl) cc prBs mrNm mrSrc $ parseSymbMap el

-- | custom xml-search for not only immediate children
deepSearch :: [String] -> Element -> [Element]
deepSearch tags' ele = rekSearch ele where
  tags = map unqual tags'
  rekSearch e = filtr e ++ concatMap filtr (elChildren e)
  filtr = filterChildrenName (`elem` tags)

readEdgeId :: String -> EdgeId
readEdgeId = EdgeId . fromMaybe (-1) . readMaybe
