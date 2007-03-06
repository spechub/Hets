{-# OPTIONS -fallow-undecidable-instances #-}
{- |
Module      :  $Header$
Description :  Instance of class Logic for propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@tzi.de
Stability   :  experimental
Portability :  portable

Basic and static analysis for propositional logic

  Ref.
  <http://en.wikipedia.org/wiki/Propositional_logic>
-}
	
module Propositional.Analysis 
    (
     basicPropositionalAnalysis
    )
    where

import qualified Propositional.AS_BASIC_Propositional as AS_BASIC
import qualified Propositional.Sign as Sign
import qualified Common.GlobalAnnotations as GlobalAnnos
import qualified Common.AS_Annotation as AS_Anno
import qualified Common.Result as Result
import qualified Common.Id as Id
import qualified Data.List as List
import qualified Data.Set as Set
import Common.Doc()
import Common.DocUtils

data DIAG_FORM = DiagForm 
    {
      formula :: AS_Anno.Named (AS_BASIC.FORMULA),
      diagnosis :: Result.Diagnosis
    }

-- | Retrieves the signature out of a basic spec
makeSig :: 
    AS_BASIC.BASIC_SPEC                  -- Input SPEC
    -> Sign.Sign                         -- Input Signature
    -> Sign.Sign                         -- Output Signature
makeSig (AS_BASIC.Basic_spec spec) sig = List.foldl retrieveBasicItem sig spec

-- Helper for makeSig
retrieveBasicItem :: 
    Sign.Sign                                     -- Input Signature
    -> AS_Anno.Annoted (AS_BASIC.BASIC_ITEMS)     -- Input Item
    -> Sign.Sign                                  -- Output Signature
retrieveBasicItem sig x = 
    case (AS_Anno.item x) of
      (AS_BASIC.Pred_decl apred) -> List.foldl 
                                    (\asig ax-> Sign.addToSig asig $ Id.simpleIdToId ax) 
                                    sig $ (\(AS_BASIC.Pred_item xs _)-> xs) apred
      (AS_BASIC.Axiom_items _)   -> sig

-- | Retrieve the formulas out of a basic spec
makeFormulas :: 
    AS_BASIC.BASIC_SPEC
    -> Sign.Sign
    -> [DIAG_FORM]
makeFormulas (AS_BASIC.Basic_spec bspec) sig = List.foldl (\xs bs -> retrieveFormulaItem xs bs sig) []  bspec

-- Helper for makeFormulas
retrieveFormulaItem :: 
    [DIAG_FORM]
    -> AS_Anno.Annoted (AS_BASIC.BASIC_ITEMS)
    -> Sign.Sign
    -> [DIAG_FORM]
retrieveFormulaItem axs x sig = 
    case (AS_Anno.item x) of 
      (AS_BASIC.Pred_decl _)    -> axs 
      (AS_BASIC.Axiom_items ax) -> List.foldl (\xs bs -> addFormula xs bs sig) axs $ numberFormulae ax 0

-- Number formulae
numberFormulae :: [AS_Anno.Annoted (AS_BASIC.FORMULA)] -> Integer -> [(AS_Anno.Annoted (AS_BASIC.FORMULA), Integer)]
numberFormulae [] _ = []
numberFormulae (x:xs) i 
    | label == "" =  (x, i) : (numberFormulae xs $ i + 1)
    | otherwise   =  (x, 0) : (numberFormulae xs $ i)
    where
      label = AS_Anno.getRLabel x

--  Add a formula to a named list of formulas
addFormula :: [DIAG_FORM]
           -> (AS_Anno.Annoted (AS_BASIC.FORMULA), Integer) 
           -> Sign.Sign
           -> [DIAG_FORM]             
addFormula formulae (f, i) sign
    | isLegal == True = formulae ++ [DiagForm
                                     {
                                       formula   = makeNamed f i
                                     , diagnosis = Result.Diag 
                                                   {
                                                     Result.diagKind = Result.Hint
                                                   , Result.diagString = "All fine"
                                                   , Result.diagPos    = Id.nullRange
                                                   }
                                     }] 
    | otherwise       = formulae ++ [DiagForm
                                     {
                                       formula   = makeNamed f i
                                     , diagnosis = Result.Diag 
                                                   {
                                                     Result.diagKind = Result.Error
                                                   , Result.diagString = "Unknown propositions "
                                                     ++ (show $ pretty difference)
                                                     ++ "in formula "
                                                     ++ (show $ pretty nakedFormula)
                                                   , Result.diagPos    = Id.nullRange
                                                   }
                                     }] 
    where
      nakedFormula  = AS_Anno.item f
      varsOfFormula = propsOfFormula nakedFormula
      isLegal       = Sign.isSubSigOf varsOfFormula sign
      difference    = Sign.sigDiff varsOfFormula sign

-- generates a named formula
makeNamed :: AS_Anno.Annoted (AS_BASIC.FORMULA) -> Integer -> AS_Anno.Named (AS_BASIC.FORMULA)
makeNamed f i 
    | label == "" = AS_Anno.NamedSen
                    {
                      AS_Anno.senName = "Ax_" ++ show i
                    , AS_Anno.isAxiom = True
                    , AS_Anno.isDef   = False
                    , AS_Anno.sentence = AS_Anno.item f
                    }
    | otherwise   = AS_Anno.NamedSen
                    {
                      AS_Anno.senName = label
                    , AS_Anno.isAxiom = True
                    , AS_Anno.isDef   = False
                    , AS_Anno.sentence = AS_Anno.item f
                    }
    where 
      label = AS_Anno.getRLabel f

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

-- Basic analysis for propostional logic
basicAnalysis :: AS_BASIC.BASIC_SPEC 
              -> Sign.Sign
              -> GlobalAnnos.GlobalAnnos
              -> Result.Result (
                                AS_BASIC.BASIC_SPEC
                               ,Sign.Sign
                               ,[AS_Anno.Named (AS_BASIC.FORMULA)]
                               )
basicAnalysis bs sig _ 
    | exErrs == False =  Result.Result diags $ Just (bs, bsSig, formulae)
    | otherwise       =  Result.Result diags $ Nothing
    where 
      bsSig     = makeSig bs sig
      bsForm    = makeFormulas bs bsSig
      formulae  = map (\x -> formula x) bsForm
      diags     = map (\x -> diagnosis x) bsForm   
      exErrs    = Result.hasErrors diags

-- | Wrapper for the interface defined in Logic.Logic
basicPropositionalAnalysis :: (
                               AS_BASIC.BASIC_SPEC
                              , Sign.Sign
                              , GlobalAnnos.GlobalAnnos
                              )
                           -> Result.Result (
                                             AS_BASIC.BASIC_SPEC
                                            ,Sign.Sign
                                            ,[AS_Anno.Named (AS_BASIC.FORMULA)]
                                            )
basicPropositionalAnalysis (bs, sig, ga) = basicAnalysis bs sig ga
