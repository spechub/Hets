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
    , pROPsen_analysis
    )
    where

import Common.ExtSign
import Common.Doc
import Common.Lib.Graph
import Common.SetColimit
import Data.Graph.Inductive.Graph
import Data.Maybe (fromJust)
import NeSyPatterns.Sign as Sign
import qualified Common.AS_Annotation as AS_Anno
import qualified Common.GlobalAnnotations as GlobalAnnos
import qualified Common.Id as Id
import qualified Common.Result as Result
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified NeSyPatterns.AS as AS
import qualified NeSyPatterns.Morphism as Morphism
import qualified NeSyPatterns.Symbol as Symbol

data TEST_SIG = TestSig
    {
      msign :: Sign.Sign
    , tdiagnosis :: [Result.Diagnosis]
    -- , ids :: Set.Set Id.Token
    , idMap :: Map.Map Id.Token Id.Token -- Maps a nesy id to its ontolgy term
    }

-- | Retrieves the signature out of a basic spec
makeSig ::
    AS.BASIC_SPEC                         -- Input SPEC
    -> Sign.Sign                          -- Input Signature
    -> TEST_SIG                           -- Output Signature
makeSig bs@(AS.Basic_spec spec) sig = let spec' = genIds spec in
  List.foldl retrieveBasicItem TestSig {
      msign = sig
    , tdiagnosis = []
    , idMap = extractIdMap bs
    } spec' 

extractIdMap :: AS.BASIC_SPEC -> Map.Map Id.Token Id.Token
extractIdMap (AS.Basic_spec spec) = foldr idMapP Map.empty spec where
  idMapP :: AS.BASIC_ITEM -> Map.Map Id.Token Id.Token -> Map.Map Id.Token Id.Token
  idMapP (AS.Path nodes) m = foldr idMapN m nodes

  idMapN :: AS.Node -> Map.Map Id.Token Id.Token -> Map.Map Id.Token Id.Token
  idMapN node m = case (ontologyTerm node, nesyId node) of
    (Just o, Just i) -> Map.insert i o m
    (Nothing, Nothing) -> m


addError :: (Id.GetRange a, Pretty a) => String -> a -> TEST_SIG -> TEST_SIG
addError s n t = t {
  tdiagnosis = tdiagnosis t ++ [mkError s n]
}

genIds :: AS.BASIC_SPEC -> AS.BASIC_SPEC
genIds (AS.Basic_spec paths) = AS.Basic_spec $ snd $ foldl genIdsPath (0, []) paths

genIdsPath :: AS.BASIC_ITEM -> (Int, [AS.BASIC_ITEM]) -> (Int, [AS.BASIC_ITEM])
genIdsPath (AS.Path nodes) (genId, agg) = Path <$> foldl genIdsNode ([], genId) nodes

genIdsNode :: AS.Node -> (Int, [AS.Node]) -> (Int, [AS.Node])
genIdsNode node (genId, agg) = case (ontologyTerm node, nesyId node) of
  (Just _, Nothing) -> (genId + 1, node { AS.nesyId = mkNumVar "__genid" genId } : agg)
  _ -> (genId, node : agg)


-- Helper for makeSig
retrieveBasicItem ::
    TEST_SIG                                      -- Input Signature
    -> AS_Anno.Annoted AS.BASIC_ITEM              -- Input Item
    -> TEST_SIG                                   -- Output Signature
retrieveBasicItem tsig x = let sig = msign tsig in case AS_Anno.item x of
      AS.Path [] -> tsig
      AS.Path nodes@(n0:_) ->
        foldl (retrieveNode tsig n0) (\(tsig', fM) t -> case fM of
          Nothing -> (tsig', Nothing) -- If an error occured for the previous node, abort
          Just f -> tsig' {
            msign = addEdgeToSig (f, retrieveNode t) sig
          }) nodes

resolveNode :: TEST_SIG -> AS.Node -> (TEST_SIG, ResolvedNode)
resolveNode tsig n = 
  let sig = msig tsig
      mkRNode o i = ResolvedNode o i (getRange n)
  in case (ontologyTerm n, nesyId n) of
    (Nothing, Nothing) -> (addError "Invalid configuration for node. Either an ontoloty term or an id has to be specified" n tsig, Nothing)
    (Just o, Just i) ->  let r = mkRNode o i in (tsig { msign = addToSig r}, r)
    (Just o, Nothing) -> (addError "Unset nesyid." n tsig, Nothing)
    (Nothing, Just i) -> case Map.lookup i (idMap tsig) of
      Just o -> let r = mkRNode o i in (tsig { msign = addToSig r}, r)
      Nothing -> (addError ("Undefined id '" ++ show i ++ "'." n) tsig, Nothing)

-- Basic analysis 
basicNeSyPatternsAnalysis
  :: (AS.BASIC_SPEC, Sign.Sign, GlobalAnnos.GlobalAnnos)
  -> Result.Result (AS.BASIC_SPEC,
                    ExtSign Sign.Sign AS.Node,
                    [AS_Anno.Named AS.Node])
basicNeSyPatternsAnalysis (bs, sig, _) =
   Result.Result diags $ if exErrs then Nothing else
     Just (bs, ExtSign sigItems declaredSyms, formulae)
    where
      bsSig = makeSig bs sig
      sigItems = msign bsSig
      declaredSyms = Set.map AS.Node
        $ Set.difference (Sign.nodes sigItems) $ nodes sig
      bsForm = makeFormulas bs sigItems
      formulae = map formula bsForm
      diags = map diagnosis bsForm ++ tdiagnosis bsSig
      exErrs = Result.hasErrors diags

-- | Static analysis for symbol maps
mkStatSymbMapItem :: [AS.SYMB_MAP_ITEMS]
                  -> Result.Result (Map.Map AS.Node AS.Node)
mkStatSymbMapItem xs =
    Result.Result
    {
      Result.diags = []
    , Result.maybeResult = Just $
                           foldl
                           (
                            \ smap x ->
                                case x of
                                  AS.Symb_map_items sitem _ ->
                                       Map.union smap $ statSymbMapItem sitem
                           )
                           Map.empty
                           xs
    }

statSymbMapItem :: [AS.SYMB_OR_MAP]
                 -> Map.Map AS.Node AS.Node
statSymbMapItem =
    foldl
    (
     \ mmap x ->
         case x of
           AS.Symb sym ->
               Map.insert (symbToSymbol sym) (symbToSymbol sym) mmap
           AS.Symb_map s1 s2 _ ->
               Map.insert (symbToSymbol s1) (symbToSymbol s2) mmap
    )
    Map.empty

-- | Retrieve raw symbols
mkStatSymbItems :: [AS.SYMB_ITEMS] -> Result.Result [Symbol.Symbol]
mkStatSymbItems a = Result.Result
                    {
                      Result.diags = []
                    , Result.maybeResult = Just $ statSymbItems a
                    }

statSymbItems :: [AS.SYMB_ITEMS] -> [Symbol.Symbol]
statSymbItems = concatMap symbItemsToSymbol

symbItemsToSymbol :: AS.SYMB_ITEMS -> [Symbol.Symbol]
symbItemsToSymbol (AS.Symb_items syms _) = map symbToSymbol syms

symbToSymbol :: AS.SYMB -> Symbol.Symbol
symbToSymbol (AS.Symb_id tok) =
    Symbol.Symbol {Symbol.symName = Id.simpleIdToId tok}

makePMap :: Map.Map Symbol.Symbol Symbol.Symbol -> Sign.Sign
  -> Map.Map Node Node
makePMap imap sig = Set.fold ( \ x ->
  let symOf = Symbol.Symbol { Symbol.symName = x }
      y = Symbol.symName $ Symbol.applySymMap imap symOf
  in Map.insert x y ) Map.empty $ Sign.nodes sig

-- | Induce a signature morphism from a source signature and a raw symbol map
inducedFromMorphism :: Map.Map Symbol.Symbol Symbol.Symbol
                    -> Sign.Sign
                    -> Result.Result Morphism.Morphism
inducedFromMorphism imap sig = let pMap = makePMap imap sig in
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
                  sigItems = Sign.nodes sig
                  pMap :: Map.Map Node Node
                  pMap = Set.fold ( \ x ->
                    let symOf = Symbol.Symbol { Symbol.symName = x }
                        y = Symbol.symName $ Symbol.applySymMap imap symOf
                    in Map.insert x y ) Map.empty sigItems
                  targetSig = Sign.Sign
                    { Sign.nodes = Set.map (Morphism.applyMap pMap)
                      $ Sign.nodes sig }
                  isSub = Sign.nodes targetSig `Set.isSubsetOf` Sign.nodes tSig
              in if isSub then return Morphism.Morphism
                     { Morphism.source = sig
                     , Morphism.nodeMap = makePMap imap sig
                     , Morphism.target = tSig
                     }
                     else fail "Incompatible mapping"

signatureColimit :: Gr Sign.Sign (Int, Morphism.Morphism)
                 -> Result.Result (Sign.Sign, Map.Map Int Morphism.Morphism)
signatureColimit graph = do
 let graph1 = nmap Sign.nodes $ emap (\ (x, y) -> (x, Morphism.nodeMap y)) graph
     (set, maps) = addIntToSymbols $ computeColimitSet graph1
     cSig = Sign.Sign {Sign.nodes = set}
 return (cSig,
         Map.fromList $ map (\ (i, n) ->
                              (i, Morphism.Morphism {
                                    Morphism.source = n,
                                    Morphism.target = cSig,
                                    Morphism.nodeMap = maps Map.! i
                                  })) $ labNodes graph)


