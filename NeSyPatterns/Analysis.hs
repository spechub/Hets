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
    )
    where

import Common.ExtSign
import Common.DocUtils
import Common.Lib.Graph
import Common.SetColimit
import Data.Graph.Inductive.Graph
import Data.Maybe (fromJust, catMaybes)
import Data.Foldable (foldrM)
import NeSyPatterns.Sign as Sign
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
      AS.Path nodes@(n0:_) -> do
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
                          , Morphism.nodeMap = pMap
                          , Morphism.target = Sign.Sign
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
                    Sign.nodes = Set.empty, -- Set.map (Morphism.applyMap pMap) $ Sign.nodes sig,
                    Sign.edges = Rel.empty,
                    Sign.idMap = Map.empty } -- TODO: IMPLEMENT
                  isSub = Sign.nodes targetSig `Set.isSubsetOf` Sign.nodes tSig
              in if isSub then return Morphism.Morphism
                     { Morphism.source = sig
                     , Morphism.nodeMap = makePMapR imap sig
                     , Morphism.target = tSig
                     }
                     else fail "Incompatible mapping"

signatureColimit :: Gr Sign.Sign (Int, Morphism.Morphism)
                 -> Result.Result (Sign.Sign, Map.Map Int Morphism.Morphism)
signatureColimit graph = do
  fail "NOT IMPLEMENTED"
--  let graph1 = nmap Sign.nodes $ emap (\ (x, y) -> (x, Morphism.nodeMap y)) graph
--      (set, maps) = addIntToSymbols $ computeColimitSet graph1
--      cSig = Sign.Sign {Sign.nodes = set}
--  return (cSig,
--          Map.fromList $ map (\ (i, n) ->
--                               (i, Morphism.Morphism {
--                                     Morphism.source = n,
--                                     Morphism.target = cSig,
--                                     Morphism.nodeMap = maps Map.! i
--                                   })) $ labNodes graph)


