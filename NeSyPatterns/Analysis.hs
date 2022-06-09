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
import Common.Lib.Graph
import Common.SetColimit
import Data.Graph.Inductive.Graph
import NeSyPatterns.Sign as Sign
import qualified Common.AS_Annotation as AS_Anno
import qualified Common.GlobalAnnotations as GlobalAnnos
import qualified Common.Id as Id
import qualified Common.Result as Result
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified NeSyPatterns.AS_NeSyPatterns as AS
import qualified NeSyPatterns.Morphism as Morphism
import qualified NeSyPatterns.Symbol as Symbol

data TEST_SIG = TestSig
    {
      msign :: Sign.Sign
    , occurence :: Int
    , tdiagnosis :: [Result.Diagnosis]
    }

-- | Retrieves the signature out of a basic spec
makeSig ::
    AS.BASIC_SPEC                  -- Input SPEC
    -> Sign.Sign                         -- Input Signature
    -> TEST_SIG                          -- Output Signature
makeSig (AS.Basic_spec spec) sig = List.foldl retrieveBasicItem
                                         TestSig { msign = sig
                                                 , occurence = 0
                                                 , tdiagnosis = []
                                                 }
                                         spec

-- Helper for makeSig
retrieveBasicItem ::
    TEST_SIG                                      -- Input Signature
    -> AS_Anno.Annoted AS.BASIC_ITEMS       -- Input Item
    -> TEST_SIG                                   -- Output Signature
retrieveBasicItem tsig x =
    let
        occ = occurence tsig
        nocc = occ == 0
    in
    case AS_Anno.item x of
      AS.Pred_decl apred -> List.foldl (\ asig ax -> TestSig
        { msign = Sign.addToSig (msign asig) $ Id.simpleIdToId ax
        , occurence = occ
        , tdiagnosis = tdiagnosis tsig ++
            [ Result.Diag
              { Result.diagKind = if nocc then Result.Hint else Result.Error
              , Result.diagString = if nocc then "All fine" else
                 "Definition of proposition " ++ show (pretty ax)
                 ++ " after first axiom"
              , Result.diagPos = AS_Anno.opt_pos x }]
        }) tsig $ (\ (AS.Pred_item xs _) -> xs) apred
      AS.Axiom_items _ -> TestSig
        { msign = msign tsig
        , occurence = occ + 1
        , tdiagnosis = tdiagnosis tsig ++
            [ Result.Diag
             { Result.diagKind = Result.Hint
             , Result.diagString = "First axiom"
             , Result.diagPos = AS_Anno.opt_pos x }]
        }


-- Basic analysis 
basicNeSyPatternsAnalysis
  :: (AS.BASIC_SPEC, Sign.Sign, GlobalAnnos.GlobalAnnos)
  -> Result.Result (AS.BASIC_SPEC,
                    ExtSign Sign.Sign Symbol.Symbol,
                    [AS_Anno.Named AS.FORMULA])
basicNeSyPatternsAnalysis (bs, sig, _) =
   Result.Result diags $ if exErrs then Nothing else
     Just (bs, ExtSign sigItems declaredSyms, formulae)
    where
      bsSig = makeSig bs sig
      sigItems = msign bsSig
      declaredSyms = Set.map Symbol.Symbol
        $ Set.difference (nodes sigItems) $ nodes sig
      bsForm = makeFormulas bs sigItems
      formulae = map formula bsForm
      diags = map diagnosis bsForm ++ tdiagnosis bsSig
      exErrs = Result.hasErrors diags

-- | Static analysis for symbol maps
mkStatSymbMapItem :: [AS.SYMB_MAP_ITEMS]
                  -> Result.Result (Map.Map Symbol.Symbol Symbol.Symbol)
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
                 -> Map.Map Symbol.Symbol Symbol.Symbol
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


