{-# LINE 1 "Reduce/Analysis.hs" #-}
{- |
Module      :  $Header$
Description :  Abstract syntax for reduce
Copyright   :  (c) Dominik Dietrich, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  dominik.dietrich@dfki.de
Stability   :  experimental
Portability :  portable

-}


module Propositional.Analysis
    (
     basicPropositionalAnalysis
    ,mkStatSymbItems
    ,mkStatSymbMapItem
    ,inducedFromMorphism
    ,inducedFromToMorphism
    , signatureColimit
    )
    where

import Common.ExtSign
import Common.Lib.Graph
import Common.SetColimit
import Data.Graph.Inductive.Graph
import Reduce.Sign as Sign
import qualified Common.AS_Annotation as AS_Anno
import qualified Common.GlobalAnnotations as GlobalAnnos
import qualified Common.Id as Id
import qualified Common.Result as Result
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Reduce.AS_BASIC_Reduce 
import Reduce.Morphism 
import Reduce.Symbol 


-- | Datatype for formulas with diagnosis data
data DIAG_FORM = DiagForm
    {
      formula :: AS_Anno.Named (CMD),
      diagnosis :: Result.Diagnosis
    }


-- | Retrieve the formulas out of a basic spec
getFormulasfromSpec :: BASIC_SPEC -> Sign.Sign -> [DIAG_FORM]
getFormulasfromSpec (Basic_spec bspec) sig =
    List.foldl (\xs bs -> retrieveFormulaItem xs bs sig) []  bspec

-- | takes a list of axioms, a new entry of a basic spec to be analyzed, and the current signature
-- and returns the new list of axioms
analyzeAndExtendAxioms ::[DIAG_FORM] -> AS_Anno.Annoted (BASIC_ITEMS) -> Sign.Sign -> [DIAG_FORM]
analyzeAndExtendAxioms axs x sig =
    case (AS_Anno.item x) of
      (Op_decl _)    -> axs
      (Axiom_items ax) ->
          List.foldl (\xs bs -> addFormula xs bs sig) axs $ numberFormulae ax 0


-- | stepwise extends an initially empty signature by the basic spec bs. The resulting spec contains analyzed axioms in it. 
-- The result contains: 1) the basic spec 2) the new signature + the added symbols 3) sentences of the spec 
basicPropositionalAnalysis (bs, sig, _) =
   Result.Result diags $ if exErrs then Nothing else
     Just (bs, ExtSign sigItems declaredSyms, formulae)
    where
      bsSig     = makeSig bs sig
      sigItems  = msign bsSig
      declaredSyms = Set.map Symbol.Symbol
        $ Set.difference (items sigItems) $ items sig
      bsForm    = makeFormulas bs sigItems
      formulae  = map formula bsForm
      diags     = map diagnosis bsForm ++ tdiagnosis bsSig
      exErrs    = Result.hasErrors diags


mkStatSymbMapItem :: [AS_BASIC.SYMB_MAP_ITEMS]
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
                                  AS_BASIC.Symb_map_items sitem _ ->
                                       Map.union smap $ statSymbMapItem sitem
                           )
                           Map.empty
                           xs
    }


-- | Retrieve raw symbols
mkStatSymbItems :: [AS_BASIC.SYMB_ITEMS] -> Result.Result [Symbol.Symbol]
mkStatSymbItems a = Result.Result
                    {
                      Result.diags = []
                    , Result.maybeResult = Just $ statSymbItems a
                    }


statSymbMapItem :: [AS_BASIC.SYMB_OR_MAP]
                -> Map.Map Symbol.Symbol Symbol.Symbol
statSymbMapItem xs =
    foldl
    (
     \ mmap x ->
         case x of
           AS_BASIC.Symb sym -> Map.insert (symbToSymbol sym) (symbToSymbol sym) mmap
           AS_BASIC.Symb_map s1 s2 _
             -> Map.insert (symbToSymbol s1) (symbToSymbol s2) mmap
    )
    Map.empty
    xs


-- | Induce a signature morphism from a source signature and a raw symbol map
inducedFromMorphism :: Map.Map Symbol.Symbol Symbol.Symbol
                    -> Sign.Sign
                    -> Result.Result Morphism.Morphism
inducedFromMorphism imap sig =
    Result.Result
          {
            Result.diags = []
          , Result.maybeResult =
              let
                  sigItems = Sign.items sig
                  pMap:: Map.Map Id.Id Id.Id
                  pMap =
                      Set.fold (
                                \ x ->
                                    let
                                        symOf = Symbol.Symbol { Symbol.symName = x }
                                        y = Symbol.symName $ Symbol.applySymMap imap symOf
                                    in
                                      Map.insert x y
                               )
                               Map.empty sigItems
              in
              Just
              Morphism.Morphism
                          {
                            Morphism.source  = sig
                          , Morphism.propMap = pMap
                          , Morphism.target  = Sign.Sign
                                               {Sign.items =
                                                    Set.map (Morphism.applyMap pMap) $
                                                       Sign.items sig
                                               }
                          }
          }

-- | Induce a signature morphism from a source signature and a raw symbol map
inducedFromToMorphism :: Map.Map Symbol.Symbol Symbol.Symbol
                    -> ExtSign Sign.Sign Symbol.Symbol
                    -> ExtSign Sign.Sign Symbol.Symbol
                    -> Result.Result Morphism.Morphism
inducedFromToMorphism imap (ExtSign sig _) (ExtSign tSig _) =
              let
                  sigItems = Sign.items sig
                  pMap:: Map.Map Id.Id Id.Id
                  pMap =
                      Set.fold (
                                \ x ->
                                    let
                                        symOf = Symbol.Symbol { Symbol.symName = x }
                                        y = Symbol.symName $ Symbol.applySymMap imap symOf
                                    in
                                      Map.insert x y
                               )
                               Map.empty sigItems
                  targetSig = Sign.Sign
                                               {Sign.items =
                                                    Set.map (Morphism.applyMap pMap) $
                                                       Sign.items sig
                                               }
                  isSub = (Sign.items targetSig) `Set.isSubsetOf` (Sign.items tSig)
              in
                case isSub of
                     True ->     Result.Result
                                 {
                                   Result.diags = []
                                 , Result.maybeResult =
                                     Just
                                     Morphism.Morphism
                                                 {
                                                   Morphism.source  = sig
                                                 , Morphism.propMap = pMap
                                                 , Morphism.target  = tSig
                                                 }
                                 }
                     False -> Result.Result
                              {
                                Result.diags =
                                [
                                 Result.Diag
                                       {
                                         Result.diagKind   = Result.Error
                                       , Result.diagString = "Incompatible mapping"
                                       , Result.diagPos    = Id.nullRange
                                       }
                                ]
                              , Result.maybeResult = Nothing
                              }

signatureColimit :: Gr Sign.Sign (Int, Morphism.Morphism)
                 -> Result.Result (Sign.Sign, Map.Map Int Morphism.Morphism)
signatureColimit graph = do
 let graph1 = nmap Sign.items $ emap (\(x,y) -> (x, Morphism.propMap y)) graph
     (set, maps) = addIntToSymbols $ computeColimitSet graph1
     cSig = Sign.Sign{Sign.items = set}
 return (cSig,
         Map.fromList $ map (\(i, n) ->
                              (i, Morphism.Morphism{
                                    Morphism.source = n,
                                    Morphism.target = cSig,
                                    Morphism.propMap = maps Map.! i
                                  }))$ labNodes graph)

