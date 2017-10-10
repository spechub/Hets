{- |
Module      :  ./HPL/Analysis.hs
Description :  Basic analysis for propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Basic and static analysis for hybrid propositional logic

-}

module HPL.Analysis
    ( basicHPLAnalysis
    --, mkStatSymbItems
    --, mkStatSymbMapItem
    --, inducedFromMorphism
    --, inducedFromToMorphism
    --, signatureColimit
    --, pROPsen_analysis
    )
    where

import Debug.Trace

import Common.ExtSign
import Common.Lib.Graph
import Common.SetColimit
import Data.Graph.Inductive.Graph
import qualified Propositional.Sign as PSign
import qualified Common.AS_Annotation as AS_Anno
import qualified Common.GlobalAnnotations as GlobalAnnos
import qualified Common.Id as Id
import qualified Common.Result as Result
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Propositional.AS_BASIC_Propositional as PBasic
import qualified Propositional.Morphism as PMorphism
import qualified Propositional.Symbol as PSymbol
import qualified Propositional.Analysis as PAnalysis


import qualified HPL.Sign as HSign
import qualified HPL.Morphism as HMorphism
import qualified HPL.Symbol as HSymbol
import qualified HPL.AS_BASIC_HPL as HBasic

-- | Datatype for formulas with diagnosis data
data DIAG_FORM = DiagForm
    {
      formula :: AS_Anno.Named HBasic.FORMULA,
      diagnosis :: Result.Diagnosis
    }

-- | Formula annotated with a number
data NUM_FORM = NumForm
    {
      nfformula :: AS_Anno.Annoted HBasic.FORMULA
    , nfnum :: Integer
    }

data TEST_SIG = TestSig
    {
      msign :: HSign.HSign
    , occurence :: Int
    , tdiagnosis :: [Result.Diagnosis]
    }

-- | Retrieves the signature out of a basic spec
makeSig ::
    HBasic.BASIC_SPEC                    -- Input SPEC
    -> HSign.HSign                        -- Input Signature
    -> TEST_SIG                          -- Output Signature
makeSig (HBasic.Basic_spec spec) sig = List.foldl retrieveBasicItem
                                         TestSig { msign = sig
                                                 , occurence = 0
                                                 , tdiagnosis = []
                                                 }
                                         spec

-- Helper for makeSig
retrieveBasicItem ::
    TEST_SIG                                      -- Input Signature
    -> AS_Anno.Annoted HBasic.BASIC_ITEMS         -- Input Item
    -> TEST_SIG                                   -- Output Signature
retrieveBasicItem tsig x =
    let
        occ = occurence tsig
        nocc = occ == 0
    in
    case AS_Anno.item x of
      HBasic.Pred_decl apred -> List.foldl (\ asig ax -> TestSig
        { msign = HSign.addPropToSig (msign asig) $ Id.simpleIdToId ax
        , occurence = occ
        , tdiagnosis = tdiagnosis tsig ++
            [ Result.Diag
              { Result.diagKind = if nocc then Result.Hint else Result.Error
              , Result.diagString = if nocc then "All fine" else
                 "Definition of proposition " ++ show (HSymbol.pretty ax)
                 ++ " after first axiom"
              , Result.diagPos = AS_Anno.opt_pos x }]
        }) tsig $ (\ (PBasic.Pred_item xs _) -> xs) apred
      HBasic.Nom_decl apred -> List.foldl (\ asig ax -> TestSig
        { msign = HSign.addNomToSig (msign asig) $ Id.simpleIdToId ax
        , occurence = occ
        , tdiagnosis = tdiagnosis tsig ++
            [ Result.Diag
              { Result.diagKind = if nocc then Result.Hint else Result.Error
              , Result.diagString = if nocc then "All fine" else
                 "Definition of state " ++ show (HSymbol.pretty ax)
                 ++ " after first axiom"
              , Result.diagPos = AS_Anno.opt_pos x }]
        }) tsig $ (\ (HBasic.Nom_item xs _) -> xs) apred
      HBasic.Axiom_items _ -> TestSig
        { msign = msign tsig
        , occurence = occ + 1
        , tdiagnosis = tdiagnosis tsig ++
            [ Result.Diag
             { Result.diagKind = Result.Hint
             , Result.diagString = "First axiom"
             , Result.diagPos = AS_Anno.opt_pos x }]
        }

-- | Retrieve the formulas out of a basic spec
-- this method should correct nominals as sentences?
makeFormulas ::
    HBasic.BASIC_SPEC
    -> HSign.HSign
    -> [DIAG_FORM]
makeFormulas (HBasic.Basic_spec bspec) sig =
    List.foldl (\ xs bs -> retrieveFormulaItem xs bs sig) [] bspec

-- Helper for makeFormulas
retrieveFormulaItem ::
    [DIAG_FORM]
    -> AS_Anno.Annoted HBasic.BASIC_ITEMS
    -> HSign.HSign
    -> [DIAG_FORM]
retrieveFormulaItem axs x sig =
    case AS_Anno.item x of
      HBasic.Pred_decl _ -> axs
      HBasic.Nom_decl _ -> axs
      HBasic.Axiom_items ax ->
          List.foldl (\ xs bs -> addFormula xs bs sig) axs $ numberFormulae ax 0

-- Number formulae
numberFormulae :: [AS_Anno.Annoted HBasic.FORMULA] -> Integer -> [NUM_FORM]
numberFormulae [] _ = []
numberFormulae (x : xs) i
    | label == "" = NumForm {nfformula = x, nfnum = i}
                    : numberFormulae xs (i + 1)
    | otherwise = NumForm {nfformula = x, nfnum = 0} : numberFormulae xs i
    where
      label = AS_Anno.getRLabel x

-- Add a formula to a named list of formulas
addFormula :: [DIAG_FORM]
           -> NUM_FORM
           -> HSign.HSign
           -> [DIAG_FORM]
addFormula formulae nf sign
    | isLegal = formulae ++
                        [DiagForm
                         {
                           formula = makeNamed f i
                         , diagnosis = Result.Diag
                           {
                             Result.diagKind = Result.Hint
                           , Result.diagString = "All fine"
                           , Result.diagPos = lnum
                           }
                         }]
    | otherwise = formulae ++
                        [DiagForm
                         {
                           formula = makeNamed f i
                         , diagnosis = Result.Diag
                           { Result.diagKind = Result.Error
                           , Result.diagString = "Unknown propositions "
                                         ++ show (HSymbol.pretty difference)
                                         ++ " in formula "
                                         ++ show (HSymbol.pretty nakedFormula)
                           , Result.diagPos = lnum
                           }
                         }]
    where
      f = (nfformula nf){AS_Anno.item = replaceNominals sign $ AS_Anno.item $ nfformula nf}
      i = nfnum nf
      nakedFormula = AS_Anno.item f
      varsOfFormula = propsOfFormula nakedFormula
      isLegal = HSign.isSubSigOf varsOfFormula sign
      difference = HSign.sigDiff varsOfFormula sign
      lnum = AS_Anno.opt_pos f

-- generates a named formula
makeNamed :: AS_Anno.Annoted HBasic.FORMULA -> Integer
  -> AS_Anno.Named HBasic.FORMULA
makeNamed f i = (AS_Anno.makeNamed (if label == "" then "Ax_" ++ show i
                                       else label) $ AS_Anno.item f)
                    { AS_Anno.isAxiom = not isTheorem }
    where
      label = AS_Anno.getRLabel f
      annos = AS_Anno.r_annos f
      isImplies = foldl (\ y x -> AS_Anno.isImplies x || y) False annos
      isImplied = foldl (\ y x -> AS_Anno.isImplied x || y) False annos
      isTheorem = isImplies || isImplied

-- Retrives the signature of a formula
propsOfFormula :: HBasic.FORMULA -> HSign.HSign --TODO: add missing cases
propsOfFormula (HBasic.Negation form _) = propsOfFormula form
propsOfFormula (HBasic.Implication form1 form2 _) =
  HSign.unite (propsOfFormula form1) (propsOfFormula form2)
propsOfFormula (HBasic.Equivalence form1 form2 _) =
  HSign.unite (propsOfFormula form1) (propsOfFormula form2)
propsOfFormula (HBasic.Conjunction xs _) = List.foldl
  (\ sig frm -> HSign.unite sig $ propsOfFormula frm) HSign.emptySig xs
propsOfFormula (HBasic.Disjunction xs _) = List.foldl
  (\ sig frm -> HSign.unite sig $ propsOfFormula frm) HSign.emptySig xs
propsOfFormula _ = HSign.emptySig -- TODO: this is wrong and should be removed!

-- Basic analysis for hybrid propositional logic
basicHPLAnalysis
  :: (HBasic.BASIC_SPEC, HSign.HSign, GlobalAnnos.GlobalAnnos)
  -> Result.Result (HBasic.BASIC_SPEC,
                    ExtSign HSign.HSign HSymbol.Symbol,
                    [AS_Anno.Named HBasic.FORMULA])
basicHPLAnalysis (bs, sig, _) =
   Result.Result diags $ if exErrs then Nothing else
     trace ("Sign:" ++ show sigItems ++ "\n" ++
            "Sens:" ++ show formulae)
      $ Just (bs, ExtSign sigItems declaredSyms, formulae)
    where
      bsSig = makeSig bs sig
      sigItems = msign bsSig --TODO: sigItems should not have same name for both a nominal and a proposition
      declaredSyms = Set.difference (HSymbol.symOf sigItems) $ HSymbol.symOf sig
      bsForm = makeFormulas bs sigItems
      formulae = map formula bsForm
      diags = map diagnosis bsForm ++ tdiagnosis bsSig
      exErrs = Result.hasErrors diags

replaceNominals :: HSign.HSign -> HBasic.FORMULA -> HBasic.FORMULA
replaceNominals sig sen = 
 foldl replaceNom sen $ HSign.noms sig

replaceNom :: HBasic.FORMULA -> Id.Id -> HBasic.FORMULA
replaceNom sen nom = let
  nomTok = Id.idToSimpleId nom 
 in case sen of
     HBasic.Prop_formula propForm ->
      case propForm of
       PBasic.Predication tok -> 
         if tok == nomTok then HBasic.Nominal nomTok Id.nullRange
          else sen
       _ -> sen
     HBasic.Negation sen' r -> HBasic.Negation (replaceNom sen' nom) r
     HBasic.Conjunction sens r -> HBasic.Conjunction (map (\x -> replaceNom x nom) sens) r
     HBasic.Disjunction sens r -> HBasic.Disjunction (map (\x -> replaceNom x nom) sens) r
     HBasic.Implication sen1 sen2 r -> HBasic.Implication (replaceNom sen1 nom) (replaceNom sen2 nom) r
     HBasic.Equivalence sen1 sen2 r -> HBasic.Equivalence (replaceNom sen1 nom) (replaceNom sen2 nom) r
     HBasic.AtState tok sen' r -> HBasic.AtState tok (replaceNom sen' nom) r
     HBasic.BoxFormula sen' r -> HBasic.BoxFormula (replaceNom sen' nom) r
     HBasic.DiamondFormula sen' r -> HBasic.DiamondFormula (replaceNom sen' nom) r
     _ -> sen

{-

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
statSymbMapItem =
    foldl
    (
     \ mmap x ->
         case x of
           AS_BASIC.Symb sym ->
               Map.insert (symbToSymbol sym) (symbToSymbol sym) mmap
           AS_BASIC.Symb_map s1 s2 _ ->
               Map.insert (symbToSymbol s1) (symbToSymbol s2) mmap
    )
    Map.empty

-- | Retrieve raw symbols
mkStatSymbItems :: [AS_BASIC.SYMB_ITEMS] -> Result.Result [Symbol.Symbol]
mkStatSymbItems a = Result.Result
                    {
                      Result.diags = []
                    , Result.maybeResult = Just $ statSymbItems a
                    }

statSymbItems :: [AS_BASIC.SYMB_ITEMS] -> [Symbol.Symbol]
statSymbItems = concatMap symbItemsToSymbol

symbItemsToSymbol :: AS_BASIC.SYMB_ITEMS -> [Symbol.Symbol]
symbItemsToSymbol (AS_BASIC.Symb_items syms _) = map symbToSymbol syms

symbToSymbol :: AS_BASIC.SYMB -> Symbol.Symbol
symbToSymbol (AS_BASIC.Symb_id tok) =
    Symbol.Symbol {Symbol.symName = Id.simpleIdToId tok}

makePMap :: Map.Map Symbol.Symbol Symbol.Symbol -> Sign.Sign
  -> Map.Map Id.Id Id.Id
makePMap imap sig = Set.fold ( \ x ->
  let symOf = Symbol.Symbol { Symbol.symName = x }
      y = Symbol.symName $ Symbol.applySymMap imap symOf
  in Map.insert x y ) Map.empty $ Sign.items sig

-- | Induce a signature morphism from a source signature and a raw symbol map
inducedFromMorphism :: Map.Map Symbol.Symbol Symbol.Symbol
                    -> Sign.Sign
                    -> Result.Result Morphism.Morphism
inducedFromMorphism imap sig = let pMap = makePMap imap sig in
              return
              Morphism.Morphism
                          { Morphism.source = sig
                          , Morphism.propMap = pMap
                          , Morphism.target = Sign.Sign
                            { Sign.items = Set.map (Morphism.applyMap pMap)
                              $ Sign.items sig }
                          }

-- | Induce a signature morphism from a source signature and a raw symbol map
inducedFromToMorphism :: Map.Map Symbol.Symbol Symbol.Symbol
                    -> ExtSign Sign.Sign Symbol.Symbol
                    -> ExtSign Sign.Sign Symbol.Symbol
                    -> Result.Result Morphism.Morphism
inducedFromToMorphism imap (ExtSign sig _) (ExtSign tSig _) =
              let
                  sigItems = Sign.items sig
                  pMap :: Map.Map Id.Id Id.Id
                  pMap = Set.fold ( \ x ->
                    let symOf = Symbol.Symbol { Symbol.symName = x }
                        y = Symbol.symName $ Symbol.applySymMap imap symOf
                    in Map.insert x y ) Map.empty sigItems
                  targetSig = Sign.Sign
                    { Sign.items = Set.map (Morphism.applyMap pMap)
                      $ Sign.items sig }
                  isSub = Sign.items targetSig `Set.isSubsetOf` Sign.items tSig
              in if isSub then return Morphism.Morphism
                     { Morphism.source = sig
                     , Morphism.propMap = makePMap imap sig
                     , Morphism.target = tSig
                     }
                     else fail "Incompatible mapping"

signatureColimit :: Gr Sign.Sign (Int, Morphism.Morphism)
                 -> Result.Result (Sign.Sign, Map.Map Int Morphism.Morphism)
signatureColimit graph = do
 let graph1 = nmap Sign.items $ emap (\ (x, y) -> (x, Morphism.propMap y)) graph
     (set, maps) = addIntToSymbols $ computeColimitSet graph1
     cSig = Sign.Sign {Sign.items = set}
 return (cSig,
         Map.fromList $ map (\ (i, n) ->
                              (i, Morphism.Morphism {
                                    Morphism.source = n,
                                    Morphism.target = cSig,
                                    Morphism.propMap = maps Map.! i
                                  })) $ labNodes graph)


pROPsen_analysis :: (AS_BASIC.BASIC_SPEC, Sign.Sign, AS_BASIC.FORMULA)
  -> Result.Result AS_BASIC.FORMULA
pROPsen_analysis (_, s, f) =
        let x = addFormula [] (NumForm annoF 0) s
            h = return . diagnosis . head
            g = Just . AS_Anno.sentence . formula . head
            annoF = AS_Anno.Annoted f Id.nullRange [] []
        in Result.Result (h x) (g x)

-}
