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


import Debug.Trace
import OWL2.Propositional2OWL2(tokToIRI)
import OWL2.AS(uriToTok)

import Common.ExtSign
import Common.DocUtils
import Common.Lib.Graph
import Common.SetColimit
import qualified Data.Graph.Inductive.Graph as Gr
import Data.Maybe (fromJust, catMaybes)
import Data.Foldable (foldrM, foldlM)
import NeSyPatterns.Sign as Sign

import Common.IRI (IRI)

import qualified Common.AS_Annotation as AS_Anno
import qualified Common.GlobalAnnotations as GlobalAnnos
import qualified Common.Id as Id
import qualified Common.Result as Result
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Relation as Rel
import qualified NeSyPatterns.AS as AS
import qualified NeSyPatterns.Morphism as Morphism
import qualified NeSyPatterns.Symbol as Symbol
import qualified OWL2.AS as OWL2

data TEST_SIG = TestSig
    {
      msign :: Sign.Sign
    , tdiagnosis :: [Result.Diagnosis]
    }

-- | Retrieves the signature out of a basic spec
makeSig ::
    AS.BASIC_SPEC                         -- Input SPEC
    -> Sign.Sign                          -- Input Signature
    -> Result.Result Sign.Sign                   -- Output Signature
makeSig bs@(AS.Basic_spec spec) sig = let spec' = genIds bs in
  foldrM retrieveBasicItem sig spec'

addNodeToIdMap :: AS.Node -> Map.Map Id.Token Id.Token -> Map.Map Id.Token Id.Token
addNodeToIdMap node m = case (AS.ontologyTerm node, AS.nesyId node) of
  (Just o, Just i) -> Map.insert i o m
  (Nothing, Nothing) -> m

addPathToIdMap :: AS.BASIC_ITEM -> Map.Map Id.Token Id.Token -> Map.Map Id.Token Id.Token
addPathToIdMap (AS.Path nodes) m = foldr addNodeToIdMap m nodes

extractIdMap :: AS.BASIC_SPEC -> Map.Map Id.Token Id.Token
extractIdMap (AS.Basic_spec spec) = foldr addPathToIdMap Map.empty (AS_Anno.item <$> spec)

genIds :: AS.BASIC_SPEC -> [AS.BASIC_ITEM]
genIds (AS.Basic_spec paths) = snd $ foldl genIdsPath (0, []) $ AS_Anno.item <$> paths

genIdsPath :: (Int, [AS.BASIC_ITEM]) -> AS.BASIC_ITEM -> (Int, [AS.BASIC_ITEM])
genIdsPath (genId, agg) (AS.Path nodes) = ((: agg) . AS.Path <$> foldl genIdsNode (genId, []) nodes)

genIdsNode :: (Int, [AS.Node]) -> AS.Node -> (Int, [AS.Node])
genIdsNode (genId, agg) node = case (AS.ontologyTerm node, AS.nesyId node) of
  (Just _, Nothing) -> (genId + 1, node { AS.nesyId = Just $ Id.mkNumVar "__genid" genId } : agg)
  _ -> (genId, node : agg)


-- Helper for makeSig
retrieveBasicItem ::
    AS.BASIC_ITEM              -- Input Item
    -> Sign                                          -- Input Signature
    -> Result.Result Sign                                -- Output Signature
retrieveBasicItem x sig = case x of
      AS.Path [] -> return sig
      AS.Path (n0:nodes) -> do
        n0' <- (resolveNode sig n0)
        (_, sig') <- foldrM (\t (f, s) -> do
            resolvedTo <- resolveNode sig t
            return (resolvedTo, addEdgeToSig s (f, resolvedTo))
          ) (n0', sig) nodes
        return sig'
        

resolveNode :: Sign -> AS.Node -> Result.Result ResolvedNode
resolveNode sig n = let
      mkRNode o i = ResolvedNode o i (Id.getRange n)
  in case (AS.ontologyTerm n, AS.nesyId n) of
    (Nothing, Nothing) -> Result.mkError "Invalid configuration for node. Either an ontoloty term or an id has to be specified" n
    (Just o, Just i) ->  let r = mkRNode o i in return r
    (Just o, Nothing) -> Result.mkError "Unset nesyid." n
    (Nothing, Just i) -> case Map.lookup i (idMap sig) of
      Just o -> let r = mkRNode o i in return r
      Nothing -> Result.mkError ("Undefined id '" ++ show i ++ "'.") n

-- Basic analysis 
basicNeSyPatternsAnalysis
  :: (AS.BASIC_SPEC, Sign.Sign, GlobalAnnos.GlobalAnnos)
  -> Result.Result (AS.BASIC_SPEC,
                    ExtSign Sign.Sign Symbol.Symbol,
                    [AS_Anno.Named ()])
basicNeSyPatternsAnalysis (spec@(AS.Basic_spec paths), sig, _) = do
  let idMap = extractIdMap spec
  sign <- makeSig spec sig

  return (spec, ExtSign sign (Set.map (Symbol.Symbol . resolved2Node) $ Sign.nodes sign), [])

-- | Static analysis for symbol maps
mkStatSymbMapItem :: Sign -> Maybe Sign -> [AS.SYMB_MAP_ITEMS]
                  -> Result.Result (Map.Map Symbol.Symbol Symbol.Symbol)
mkStatSymbMapItem _ _ = return . foldr
  (\(AS.Symb_map_items sitem r) -> Map.union $ statSymbMapItem sitem)
  Map.empty

statSymbMapItem :: [AS.SYMB_OR_MAP]
                 -> Map.Map Symbol.Symbol Symbol.Symbol
statSymbMapItem = foldl (\mmap x ->
         case x of
           AS.Symb sym -> Map.insert (symbToSymbol sym) (symbToSymbol sym) mmap
           AS.Symb_map s1 s2 _ ->
               Map.insert (symbToSymbol s1) (symbToSymbol s2) mmap
    ) Map.empty

-- | Retrieve raw symbols
mkStatSymbItems :: Sign.Sign -> [AS.SYMB_ITEMS] -> Result.Result [Symbol.Symbol]
mkStatSymbItems sig a = let
    tokens = [(t, Map.lookup t (Sign.idMap sig), r) | (AS.Symb_items symbs r) <- a, (AS.Symb_id t) <- symbs]
    errors =  [ Result.mkDiag Result.Error "Unknown symbol" t | (t, Nothing, _) <- tokens]
  in Result.Result errors (Just [ Symbol.Symbol $ AS.Node (Just t) o r | (t, o, r) <- tokens])

statSymbItems :: [AS.SYMB_ITEMS] -> [Symbol.Symbol]
statSymbItems = concatMap symbItemsToSymbol

symbItemsToSymbol :: AS.SYMB_ITEMS -> [Symbol.Symbol]
symbItemsToSymbol (AS.Symb_items syms _) = map symbToSymbol syms

symbToSymbol :: AS.SYMB -> Symbol.Symbol
symbToSymbol (AS.Symb_id tok) =
    Symbol.Symbol $ AS.Node Nothing (Just tok) (Id.getRange tok)


symbol2ResolvedNode :: Sign.Sign -> (Symbol.Symbol, Symbol.Symbol) -> Maybe (ResolvedNode, ResolvedNode)
symbol2ResolvedNode sig (sk, sv) = do
  k <- Result.resultToMaybe $ resolveNode sig $ Symbol.node sk
  v <- Result.resultToMaybe $ resolveNode sig $ Symbol.node sv
  return (k, v)
  

makePMapR :: Map.Map Symbol.Symbol Symbol.Symbol
  -> Sign.Sign
  -> Map.Map ResolvedNode ResolvedNode
makePMapR imap sig = Map.fromList . catMaybes . fmap (symbol2ResolvedNode sig) . Map.toList $ imap

-- | Induce a signature morphism from a source signature and a raw symbol map
inducedFromMorphism :: Map.Map Symbol.Symbol Symbol.Symbol
                    -> Sign.Sign
                    -> Result.Result Morphism.Morphism
inducedFromMorphism imap sig = let pMap = makePMapR imap sig in
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
                  pMap = makePMapR imap sig
                  targetSig = Sign.Sign {
                    Sign.owlClasses = Set.empty, --TODO
                    Sign.owlTaxonomy = Rel.empty, -- TODO
                    Sign.nodes = Set.empty, -- Set.map (Morphism.applyMap pMap) $ Sign.nodes sig,
                    Sign.edges = Rel.empty,
                    Sign.idMap = Map.empty } -- TODO: IMPLEMENT
                  isSub = Sign.nodes targetSig `Set.isSubsetOf` Sign.nodes tSig
              in if isSub then return Morphism.Morphism
                     { Morphism.source = sig
                     , Morphism.nodeMap = makePMapR imap sig
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
      let aBounds = Set.unions $ map (\x -> Rel.lookupRan x r) $ Set.toList aSet
      in trace ("aBounds:" ++ show aBounds ++ "aSet: " ++ show aSet) $ 
         if Set.isSubsetOf aBounds aSet 
            then aSet 
            else getAllBounds $ Set.union aBounds aSet
     bounds = map getAllBounds $ map (\x -> Set.union (Set.singleton x) $ Rel.lookupRan x r) $ Set.toList s
 in case bounds of
      [] -> Nothing
      aSet : sets -> 
        let intBounds = foldl Set.intersection aSet sets
        in if null intBounds then Nothing 
           else let isLB y = let notR = Set.filter (\x -> (Rel.notMember x y r) && x /= y ) intBounds 
                              in Set.null notR
                    gbs = Set.filter isLB intBounds
                in case Set.toList gbs of 
                    [x] -> Just x
                    _ -> Nothing 

allLabels :: [(Int, Set.Set ResolvedNode)] -- the graph nodes
          -> Map.Map Int (Map.Map Id.Token Id.Token) -- the structural morphisms f of the colimit on nodeIds
          -> Id.Token -- the nodeId N in the colimit 
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
                 Gr.emap (\(x,y) -> (x, Morphism.owlMap y)) graph
      (owlC, owlMors) = addIntToSymbols $ computeColimitSet owlGraph
      owlR = colimitRel ( map(\(i, sig) -> (i, Sign.owlTaxonomy sig)) $ Gr.labNodes graph) owlMors
      graph1 = Gr.nmap (\s -> Set.map Sign.resolvedNeSyId $ Sign.nodes s) $ 
               Gr.emap (\ (x, m) -> (x, Morphism.morphism2TokenMap m)) graph
      (nodeSet, maps) = addIntToSymbols $ computeColimitSet graph1
  resSet <- foldlM (\aSet aNode -> do
                        let labSet = Set.map (tokToIRI . Sign.resolvedOTerm) $ 
                                     allLabels (map (\(i, s) -> (i, Sign.nodes s)) $ Gr.labNodes graph) maps aNode
                        case computeGLB owlR labSet of
                          Nothing -> fail "couldn't compute greatest lower bound" 
                          Just glb -> return $ Set.insert (ResolvedNode (uriToTok glb) aNode Id.nullRange) aSet    
                     ) Set.empty nodeSet
  nMaps <- foldlM (\f (i, sig) -> do
                    let fi = Map.findWithDefault (error "missing morphism") i maps
                    gi <- Morphism.tokenMap2NodeMap (Sign.nodes sig) resSet fi 
                    return $ Map.insert i gi f  
                  ) 
           Map.empty $ Gr.labNodes graph
  let edgesC = colimitRel ( map(\(i, sig) -> (i, Sign.edges sig)) $ Gr.labNodes graph) nMaps
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

