{- |
Module      :  ./NeSyPatterns/Analysis.hs
Description :  Basic analysis for propositional logic
License     :  GPLv2 or higher, see LICENSE.txt

Stability   :  experimental
Portability :  portable

Basic and static analysis for propositional logic

  Ref.
  <http://en.wikipedia.org/wiki/NeSyPatterns_logic>
-}

module NeSyPatterns.Analysis
    ( basicNeSyPatternsAnalysis
    , mkStatSymbItems
    , mkStatSymbMapItem
    , inducedFromMorphism
    , inducedFromToMorphism
    , signatureColimit
    , subClassRelation
    )
    where


import Data.Maybe (catMaybes, fromMaybe, fromJust)
import Data.Foldable (foldrM, foldlM)
import Data.List (stripPrefix)
import Data.Bifunctor (bimap, Bifunctor (second))

import Control.Applicative
import Common.ExtSign
import Common.IRI
import Common.Lib.Graph
import Common.Result (resultToMaybe)
import Common.SetColimit
import Common.Utils

import NeSyPatterns.Sign as Sign

import qualified Common.AS_Annotation as AS_Anno
import qualified Common.GlobalAnnotations as GlobalAnnos
import qualified Common.Id as Id
import qualified Common.Result as Result
import qualified Data.Graph.Inductive.Graph as Gr
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Relation as Rel
import qualified NeSyPatterns.AS as AS
import qualified NeSyPatterns.Morphism as Morphism
import qualified NeSyPatterns.Symbol as Symbol
import qualified OWL2.AS as OWL2

-- | Retrieves the signature out of a basic spec
makeSig ::
    AS.BASIC_SPEC                         -- Input SPEC
    -> Sign.Sign                          -- Input Signature
    -> Result.Result Sign.Sign                   -- Output Signature
makeSig bs sig = let spec' = genIds bs in
  foldrM retrieveBasicItem sig spec'

addNodeToIdMap :: AS.Node -> Map.Map IRI IRI -> Map.Map IRI IRI
addNodeToIdMap (AS.Node o mi _) m = case mi of
  Just i -> Map.insert i o m
  Nothing -> m

addPathToIdMap :: AS.BASIC_ITEM -> Map.Map IRI IRI -> Map.Map IRI IRI
addPathToIdMap (AS.Path ns) m = foldr addNodeToIdMap m ns

extractIdMap :: AS.BASIC_SPEC -> Map.Map IRI IRI
extractIdMap (AS.Basic_spec spec) = foldr addPathToIdMap Map.empty (AS_Anno.item <$> spec)

genIds :: AS.BASIC_SPEC -> [AS.BASIC_ITEM]
genIds (AS.Basic_spec paths) = snd $ foldr genIdsPath (0, []) $ AS_Anno.item <$> paths

genIdsPath :: AS.BASIC_ITEM -> (Int, [AS.BASIC_ITEM]) -> (Int, [AS.BASIC_ITEM])
genIdsPath (AS.Path ns) (genId, agg) = (: agg) . AS.Path <$> foldr genIdsNode (genId, []) ns

genIdsNode :: AS.Node -> (Int, [AS.Node]) -> (Int, [AS.Node])
genIdsNode node (genId, agg) = (: agg) <$> genIdNode genId node

genIdNode :: Int -> AS.Node -> (Int, AS.Node)
genIdNode genId node = case AS.nesyId node of
  Nothing -> (genId + 1, node { AS.nesyId = Just . idToIRI . Id.mkId $ [ Id.genNumVar "nesy" genId ] })
  Just _ -> (genId, node)


-- Helper for makeSig
retrieveBasicItem ::
    AS.BASIC_ITEM              -- Input Item
    -> Sign                                          -- Input Signature
    -> Result.Result Sign                                -- Output Signature
retrieveBasicItem x sig = let sigM = Just sig in case x of
      AS.Path [] -> return sig
      AS.Path ns -> do
        let n0 = last ns
        n0' <- resolveNode sigM n0
        let sig' = addToSig sig n0'
        (_, sig'') <- foldrM (\f (t, s) -> do
            resolvedFrom <- resolveNode sigM f
            return (resolvedFrom, addEdgeToSig' s (resolvedFrom, t))
          ) (n0', sig') (init ns)
        return sig''


resolveNode :: Maybe Sign -> AS.Node -> Result.Result ResolvedNode
resolveNode sigM n@(AS.Node o mi r) = case mi of
    Just i -> case sigM of
      Just sig -> if Set.member o (owlClasses sig) then
          return $ ResolvedNode o i r
        else
          Result.mkError "Undefined class" o

      Nothing -> return $ ResolvedNode o i r
    Nothing -> Result.mkError "Unset nesyid." n

-- Basic analysis 
basicNeSyPatternsAnalysis
  :: (AS.BASIC_SPEC, Sign.Sign, GlobalAnnos.GlobalAnnos)
  -> Result.Result (AS.BASIC_SPEC,
                    ExtSign Sign.Sign Symbol.Symbol,
                    [AS_Anno.Named ()])
basicNeSyPatternsAnalysis (spec, sig, _) = do
  let idm = extractIdMap spec
  sign <- makeSig spec sig { idMap = idm }
  return (spec, ExtSign sign (Set.map Symbol.Symbol $ Sign.nodes sign), [])

-- | Static analysis for symbol maps
mkStatSymbMapItem :: Sign -> Maybe Sign -> [AS.SYMB_MAP_ITEMS]
                  -> Result.Result (Map.Map Symbol.Symbol Symbol.Symbol)
mkStatSymbMapItem sig sigM = let s = maybe sig (Sign.unite Sign.emptySig) sigM in
   return . foldr
  (\(AS.Symb_map_items sitem _) -> Map.union $ statSymbMapItem s sitem)
  Map.empty

statSymbMapItem :: Sign.Sign -> [AS.SYMB_OR_MAP]
                 -> Map.Map Symbol.Symbol Symbol.Symbol
statSymbMapItem sig = foldl (\mmap x ->
         case x of
           AS.Symb sym -> Map.insert (symbToSymbol sig sym) (symbToSymbol sig sym) mmap
           AS.Symb_map s1 s2 _ ->
               Map.insert (symbToSymbol sig s1) (symbToSymbol sig s2) mmap
    ) Map.empty

-- | Retrieve raw symbols
mkStatSymbItems :: Sign.Sign -> [AS.SYMB_ITEMS] -> Result.Result [Symbol.Symbol]
mkStatSymbItems sig a = do
    resolvedSymbols <- mapM (resolveNode (Just sig)) [t | (AS.Symb_items r _) <- a, (AS.Symb_id t) <- r]
    return $ Symbol.Symbol <$> resolvedSymbols
  --   tokens = [(t, resolveNode (Just sig) t, r) | (AS.Symb_items symbs r) <- a, (AS.Symb_id t) <- symbs]
  --   errors =  [ Result.mkDiag Result.Error "Unknown symbol" t | (t, Nothing, _) <- tokens]
  -- in Result.Result errors (Just [ Symbol.Symbol $ Sign.ResolvedNode t o r | (t, o, r) <- tokens])

symbToSymbol :: Sign.Sign -> AS.SYMB -> Symbol.Symbol
symbToSymbol sig (AS.Symb_id node) = let
    resolved = resolveNode (Just sig) node
    nextId = nextGenId sig
    (_, newId) = genIdNode nextId node
    nodeM = resultToMaybe $ resolved <|> resolveNode (Just sig) newId
  in case nodeM of
    Just n -> Symbol.Symbol n
    Nothing -> error "NeSyPatterns.Analysis.symbToSymbol: Cannot convert symbol"



makePMapR :: Map.Map Symbol.Symbol Symbol.Symbol
  -> Map.Map ResolvedNode ResolvedNode
makePMapR = Map.fromList . fmap (bimap Symbol.node Symbol.node) . Map.toList

-- | Induce a signature morphism from a source signature and a raw symbol map
inducedFromMorphism :: Map.Map Symbol.Symbol Symbol.Symbol
                    -> Sign.Sign
                    -> Result.Result Morphism.Morphism
inducedFromMorphism imap sig = let pMap = makePMapR imap in
              return
              Morphism.Morphism
                          { Morphism.source = sig
                          , Morphism.owlMap = Map.empty
                          , Morphism.nodeMap = pMap
                          , Morphism.target = Sign.emptySig
                            { Sign.nodes = Set.map (Morphism.applyMap pMap)
                              $ Sign.nodes sig }
                          }

-- | Induce a signature morphism from a source signature and a raw symbol map
inducedFromToMorphism :: Map.Map Symbol.Symbol Symbol.Symbol
                    -> ExtSign Sign.Sign Symbol.Symbol
                    -> ExtSign Sign.Sign Symbol.Symbol
                    -> Result.Result Morphism.Morphism
inducedFromToMorphism imap (ExtSign sig _) (ExtSign tSig _) =
              let
                  targetSig = Sign.Sign {
                    Sign.owlClasses = Set.empty, --TODO
                    Sign.owlTaxonomy = Rel.empty, -- TODO
                    Sign.nodes = Set.empty, -- Set.map (Morphism.applyMap pMap) $ Sign.nodes sig,
                    Sign.edges = Rel.empty,
                    Sign.idMap = Map.empty } -- TODO: IMPLEMENT
                  isSub = Sign.nodes targetSig `Set.isSubsetOf` Sign.nodes tSig
              in if isSub then return Morphism.Morphism
                     { Morphism.source = sig
                     , Morphism.nodeMap = makePMapR imap
                     , Morphism.owlMap = Map.empty -- TODO
                     , Morphism.target = tSig
                     }
                     else fail "Incompatible mapping"

-- | Retrieves a relation of simple classes from a set of axioms. If (a SubClassOf b) then (a ~ b)
subClassRelation :: [OWL2.Axiom] -> Rel.Relation IRI IRI
subClassRelation axs = Rel.fromList [ (cl1, cl2) | OWL2.ClassAxiom (OWL2.SubClassOf _ (OWL2.Expression cl1) (OWL2.Expression cl2)) <- axs]

computeGLB :: (Ord a, Show a) => Rel.Relation a a -> Set.Set a -> Maybe a
computeGLB r s =
 let getAllBounds aSet =
      let aBounds = Set.unions $ map (`Rel.lookupRan` r) $ Set.toList aSet
      in if Set.isSubsetOf aBounds aSet
            then aSet
            else getAllBounds $ Set.union aBounds aSet
     bounds = map (getAllBounds . (\x -> Set.union (Set.singleton x) $ Rel.lookupRan x r)) (Set.toList s)
 in case bounds of
      [] -> Nothing
      aSet : sets ->
        let intBounds = foldl Set.intersection aSet sets
        in if null intBounds then Nothing
           else let isLB y = let notR = Set.filter (\x -> Rel.notMember x y r && x /= y ) intBounds
                              in Set.null notR
                    gbs = Set.filter isLB intBounds
                in case Set.toList gbs of
                    [x] -> Just x
                    _ -> Nothing

allLabels :: [(Int, Set.Set ResolvedNode)] -- the graph nodes
          -> Map.Map Int (Map.Map IRI IRI) -- the structural morphisms f of the colimit on nodeIds
          -> IRI -- the nodeId N in the colimit 
          -> Set.Set ResolvedNode
          -- all resolved nodes in the graph whose nodeId is mapped to N 
          -- along the corresponding morphism in f
allLabels nSets tMaps cId =
  foldl (\aSet (iMap, s) -> Set.union aSet $
                            Set.filter (\(ResolvedNode _ nId _) -> cId == Map.findWithDefault nId nId iMap) s)
        Set.empty $ map (\(i, s) -> (Map.findWithDefault (error "missing index") i tMaps, s))nSets

signatureColimit :: Gr Sign.Sign (Int, Morphism.Morphism)
                 -> Result.Result (Sign.Sign, Map.Map Int Morphism.Morphism)
signatureColimit graph = do
  let owlGraph = Gr.nmap Sign.owlClasses $
                 Gr.emap (Data.Bifunctor.second Morphism.owlMap) graph
      (owlC, owlMors) = addIntToSymbols $ computeColimitSet owlGraph
      owlR = colimitRel ( map(second owlTaxonomy) $ Gr.labNodes graph) owlMors
      graph1 = Gr.nmap (Set.map Sign.resolvedNeSyId . Sign.nodes) $
               Gr.emap (second Morphism.morphism2TokenMap) graph
      (nodeSet, maps) = addIntToSymbols $ computeColimitSet graph1
  resSet <- foldlM (\aSet aNode -> do
                        let labSet = Set.map Sign.resolvedOTerm $
                                     allLabels (map (second nodes) $ Gr.labNodes graph) maps aNode
                        case computeGLB owlR labSet of
                          Nothing -> fail "couldn't compute greatest lower bound"
                          Just glb -> return $ Set.insert (ResolvedNode glb aNode Id.nullRange) aSet
                     ) Set.empty nodeSet
  nMaps <- foldlM (\f (i, sig) -> do
                    let fi = Map.findWithDefault (error "missing morphism") i maps
                    gi <- Morphism.tokenMap2NodeMap (Sign.nodes sig) resSet fi
                    return $ Map.insert i gi f
                  )
           Map.empty $ Gr.labNodes graph
  let edgesC = colimitRel ( map(second edges) $ Gr.labNodes graph) nMaps
      colimSig = Sign{ owlClasses = owlC
                     , owlTaxonomy = owlR
                     , nodes = resSet
                     , edges = edgesC
                     , idMap = nesyIdMap resSet}
      colimMors = Map.fromList $
                  map (\(i, sig) -> let oi = Map.findWithDefault (error "owl map") i owlMors
                                        ni = Map.findWithDefault (error "node map") i nMaps
                                   in (i, Morphism.Morphism sig colimSig oi ni) ) $ Gr.labNodes graph
  return (colimSig, colimMors)

nextGenId :: Sign.Sign -> Int
nextGenId sig = foldr (\n id -> fromMaybe id $ do
      id' <- genIdFromNode n
      return $ if id' > id then id' else id
    ) 0 $ Sign.nodes sig
  where
    genIdFromNode :: Sign.ResolvedNode -> Maybe Int
    genIdFromNode n = do
      num <- stripPrefix (Id.genNamePrefix ++ "nesy") . iFragment . Sign.resolvedNeSyId $ n
      readMaybe num
