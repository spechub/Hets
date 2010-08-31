{- |
Module      :  $Header$
Description :  Basic analysis for propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Basic and static analysis for propositional logic

  Ref.
  <http://en.wikipedia.org/wiki/Propositional_logic>
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
import Propositional.Sign as Sign
import qualified Common.AS_Annotation as AS_Anno
import qualified Common.GlobalAnnotations as GlobalAnnos
import qualified Common.Id as Id
import qualified Common.Result as Result
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Propositional.AS_BASIC_Propositional as AS_BASIC
import qualified Propositional.Morphism as Morphism
import qualified Propositional.Symbol as Symbol

-- | Datatype for formulas with diagnosis data
data DIAG_FORM = DiagForm
    {
      formula :: AS_Anno.Named (AS_BASIC.FORMULA),
      diagnosis :: Result.Diagnosis
    }

-- | Formula annotated with a number
data NUM_FORM = NumForm
    {
      nfformula :: AS_Anno.Annoted (AS_BASIC.FORMULA)
    , nfnum     :: Integer
    }

data TEST_SIG = TestSig
    {
      msign :: Sign.Sign
    , occurence :: Int
    , tdiagnosis :: [Result.Diagnosis]
    }

-- | Retrieves the signature out of a basic spec
makeSig ::
    AS_BASIC.BASIC_SPEC                  -- Input SPEC
    -> Sign.Sign                         -- Input Signature
    -> TEST_SIG                          -- Output Signature
makeSig (AS_BASIC.Basic_spec spec) sig = List.foldl retrieveBasicItem
                                         (TestSig{ msign=sig
                                                 , occurence=0
                                                 , tdiagnosis = []
                                                 })
                                         spec

-- Helper for makeSig
retrieveBasicItem ::
    TEST_SIG                                      -- Input Signature
    -> AS_Anno.Annoted (AS_BASIC.BASIC_ITEMS)     -- Input Item
    -> TEST_SIG                                   -- Output Signature
retrieveBasicItem tsig x =
    let
        occ = occurence tsig
    in
    case (AS_Anno.item x) of
      (AS_BASIC.Pred_decl apred) ->
          if (occ == 0)
          then
              List.foldl
                      (\asig ax-> TestSig{
                                   msign = Sign.addToSig (msign asig) $ Id.simpleIdToId ax
                                 , occurence = occ
                                 , tdiagnosis = tdiagnosis tsig ++
                                   [Result.Diag
                                    {
                                      Result.diagKind   = Result.Hint
                                    , Result.diagString = "All fine"
                                    , Result.diagPos    = AS_Anno.opt_pos x
                                    }]
                                 })
                      tsig $ (\(AS_BASIC.Pred_item xs _)-> xs) apred
          else
              List.foldl
                      (\asig ax-> TestSig{
                                   msign = Sign.addToSig (msign asig) $ Id.simpleIdToId ax
                                 , occurence = occ
                                 , tdiagnosis = tdiagnosis tsig ++
                                   [Result.Diag
                                    {
                                      Result.diagKind   = Result.Error
                                    , Result.diagString = "Definition of proposition " ++
                                                          (show $ pretty ax) ++
                                                          " after first axiom"
                                    , Result.diagPos    = AS_Anno.opt_pos x
                                    }]
                                 })
                          tsig $ (\(AS_BASIC.Pred_item xs _)-> xs) apred
      (AS_BASIC.Axiom_items _)   -> TestSig { msign = msign tsig
                                          , occurence = occ + 1
                                          , tdiagnosis = tdiagnosis tsig ++
                                              [Result.Diag
                                               {
                                                 Result.diagKind   = Result.Hint
                                               , Result.diagString = "First axiom"
                                               , Result.diagPos    = AS_Anno.opt_pos x
                                               }]
                                            }

-- | Retrieve the formulas out of a basic spec
makeFormulas ::
    AS_BASIC.BASIC_SPEC
    -> Sign.Sign
    -> [DIAG_FORM]
makeFormulas (AS_BASIC.Basic_spec bspec) sig =
    List.foldl (\xs bs -> retrieveFormulaItem xs bs sig) []  bspec

-- Helper for makeFormulas
retrieveFormulaItem ::
    [DIAG_FORM]
    -> AS_Anno.Annoted (AS_BASIC.BASIC_ITEMS)
    -> Sign.Sign
    -> [DIAG_FORM]
retrieveFormulaItem axs x sig =
    case (AS_Anno.item x) of
      (AS_BASIC.Pred_decl _)    -> axs
      (AS_BASIC.Axiom_items ax) ->
          List.foldl (\xs bs -> addFormula xs bs sig) axs $ numberFormulae ax 0

-- Number formulae
numberFormulae :: [AS_Anno.Annoted (AS_BASIC.FORMULA)] -> Integer -> [NUM_FORM]
numberFormulae [] _ = []
numberFormulae (x:xs) i
    | label == "" =  NumForm{nfformula = x, nfnum = i} : (numberFormulae xs $ i + 1)
    | otherwise   =  NumForm{nfformula = x, nfnum = 0} : (numberFormulae xs $ i)
    where
      label = AS_Anno.getRLabel x

--  Add a formula to a named list of formulas
addFormula :: [DIAG_FORM]
           -> NUM_FORM
           -> Sign.Sign
           -> [DIAG_FORM]
addFormula formulae nf sign
    | isLegal == True = formulae ++
                        [DiagForm
                         {
                           formula   = makeNamed f i
                         , diagnosis = Result.Diag
                           {
                             Result.diagKind = Result.Hint
                           , Result.diagString = "All fine"
                           , Result.diagPos    = lnum
                           }
                         }]
    | otherwise       = formulae ++
                        [DiagForm
                         {
                           formula   = makeNamed f i
                         , diagnosis = Result.Diag
                                       {
                                         Result.diagKind = Result.Error
                                       , Result.diagString = "Unknown propositions "
                                         ++ (show $ pretty difference)
                                         ++ " in formula "
                                         ++ (show $ pretty nakedFormula)
                                       , Result.diagPos    = lnum
                                       }
                         }]
    where
      f             = nfformula nf
      i             = nfnum nf
      nakedFormula  = AS_Anno.item f
      varsOfFormula = propsOfFormula nakedFormula
      isLegal       = Sign.isSubSigOf varsOfFormula sign
      difference    = Sign.sigDiff varsOfFormula sign
      lnum          = AS_Anno.opt_pos f

-- generates a named formula
makeNamed :: AS_Anno.Annoted (AS_BASIC.FORMULA) -> Integer -> AS_Anno.Named (AS_BASIC.FORMULA)
makeNamed f i = (AS_Anno.makeNamed (if label == "" then "Ax_" ++ show i
                                       else label) $ AS_Anno.item f)
                    { AS_Anno.isAxiom = not isTheorem }
    where
      label = AS_Anno.getRLabel f
      annos = AS_Anno.r_annos f
      isImplies = foldl (\y x -> AS_Anno.isImplies x || y) False annos
      isImplied = foldl (\y x -> AS_Anno.isImplied x || y) False annos
      isTheorem = isImplies || isImplied

-- Retrives the signature of a formula
propsOfFormula :: AS_BASIC.FORMULA -> Sign.Sign
propsOfFormula (AS_BASIC.Negation form _) = propsOfFormula form
propsOfFormula (AS_BASIC.Implication form1 form2 _) = Sign.unite (propsOfFormula form1)
                                           (propsOfFormula form2)
propsOfFormula (AS_BASIC.Equivalence form1 form2 _) = Sign.unite (propsOfFormula form1)
                                           (propsOfFormula form2)
propsOfFormula (AS_BASIC.True_atom _)  = Sign.emptySig
propsOfFormula (AS_BASIC.False_atom _) = Sign.emptySig
propsOfFormula (AS_BASIC.Predication x) = Sign.Sign{Sign.items = Set.singleton $
                                                                 Id.simpleIdToId x }
propsOfFormula (AS_BASIC.Conjunction xs _) = List.foldl (\ sig frm -> Sign.unite sig $
                                                                      propsOfFormula frm)
                                             Sign.emptySig xs
propsOfFormula (AS_BASIC.Disjunction xs _) = List.foldl (\ sig frm -> Sign.unite sig $
                                                                      propsOfFormula frm)
                                             Sign.emptySig xs

-- Basic analysis for propositional logic
basicPropositionalAnalysis
  :: (AS_BASIC.BASIC_SPEC, Sign.Sign, GlobalAnnos.GlobalAnnos)
  -> Result.Result (AS_BASIC.BASIC_SPEC,
                    ExtSign Sign.Sign Symbol.Symbol,
                    [AS_Anno.Named (AS_BASIC.FORMULA)])
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

-- | Static analysis for symbol maps
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

-- | Retrieve raw symbols
mkStatSymbItems :: [AS_BASIC.SYMB_ITEMS] -> Result.Result [Symbol.Symbol]
mkStatSymbItems a = Result.Result
                    {
                      Result.diags = []
                    , Result.maybeResult = Just $ statSymbItems a
                    }

statSymbItems :: [AS_BASIC.SYMB_ITEMS] -> [Symbol.Symbol]
statSymbItems si = concat $ map symbItemsToSymbol si

symbItemsToSymbol :: AS_BASIC.SYMB_ITEMS -> [Symbol.Symbol]
symbItemsToSymbol (AS_BASIC.Symb_items syms _) = map symbToSymbol syms

symbToSymbol :: AS_BASIC.SYMB -> Symbol.Symbol
symbToSymbol (AS_BASIC.Symb_id tok) =
    Symbol.Symbol{Symbol.symName = Id.simpleIdToId tok}

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

