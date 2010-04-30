{- |
Module      :  $Header$
Description :  Basic analysis for common logic
Copyright   :  (c) Karl Luc, Uni Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  kluc@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Basic and static analysis for common logic
-}

module CommonLogic.Analysis
    (
     basicCommonLogicAnalysis
    )
    where

import Common.ExtSign
import Common.Result as Result
import CommonLogic.Sign as Sign
import CommonLogic.Symbol as Symbol
import qualified CommonLogic.AS_CommonLogic as CL
import qualified Common.AS_Annotation as AS_Anno
import qualified Common.Id as Id
import qualified Data.Set as Set
import qualified Data.List as List

data DIAG_FORM = DiagForm
    {
        formula :: AS_Anno.Named (CL.SENTENCE),
      diagnosis :: Result.Diagnosis
    }   

--retrieve sentences
makeFormulas :: CL.BASIC_SPEC -> Sign.Sign -> [DIAG_FORM]
makeFormulas (CL.Basic_spec bspec) sig = 
    List.foldl (\xs bs -> retrieveFormulaItem xs bs sig) [] bspec

retrieveFormulaItem :: [DIAG_FORM] -> AS_Anno.Annoted (CL.BASIC_ITEMS)
                       -> Sign.Sign -> [DIAG_FORM]
retrieveFormulaItem axs x sig =
   case (AS_Anno.item x) of 
      (CL.P_decl _)   -> axs
      (CL.Axiom_items ax) -> 
          List.foldl (\xs bs -> addFormula xs bs sig) axs $ numberFormulae ax 0

data NUM_FORM = NumForm
    {
      nfformula :: AS_Anno.Annoted (CL.SENTENCE)
    , nfnum     :: Int
    }

numberFormulae :: [AS_Anno.Annoted (CL.SENTENCE)] -> Int -> [NUM_FORM]
numberFormulae [] _ = []
numberFormulae (x:xs) i
    | label == "" =  NumForm{nfformula = x, nfnum = i} : (numberFormulae xs $ i + 1)
    | otherwise   =  NumForm{nfformula = x, nfnum = 0} : (numberFormulae xs $ i)
    where
      label = AS_Anno.getRLabel x

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
makeNamed :: AS_Anno.Annoted (CL.SENTENCE) -> Int -> AS_Anno.Named (CL.SENTENCE)
makeNamed f i = (AS_Anno.makeNamed (if label == "" then "Ax_" ++ show i
                                       else label) $ AS_Anno.item f)
   where
      label = AS_Anno.getRLabel f
      -- annos = AS_Anno.r_annos f
      -- isImplies = foldl (\y x -> AS_Anno.isImplies x || y) False annos
      -- isImplied = foldl (\y x -> AS_Anno.isImplied x || y) False annos
      -- isTheorem = isImplies || isImplied

-- Retrives the signature of a sentence
propsOfFormula :: CL.SENTENCE -> Sign.Sign
propsOfFormula (CL.Atom_sent form _) = case form of
                                        CL.Equation _ _ -> Sign.emptySig
                                        CL.Atom term _     -> propsOfTerm term
propsOfFormula (CL.Quant_sent _ _) = Sign.emptySig
propsOfFormula (CL.Bool_sent  _ _) = Sign.emptySig
propsOfFormula (CL.Comment_sent _ _ _) = Sign.emptySig
propsOfFormula (CL.Irregular_sent _ _) = Sign.emptySig

propsOfTerm :: CL.TERM -> Sign.Sign
propsOfTerm term = case term of
    CL.Name_term x -> Sign.Sign {Sign.items = Set.singleton $ Id.simpleIdToId x}
    CL.Funct_term _ _ _ -> Sign.emptySig 
    CL.Comment_term _ _ _ -> Sign.emptySig

basicCommonLogicAnalysis :: (CL.BASIC_SPEC, Sign.Sign, a)
  -> Result (CL.BASIC_SPEC, 
             ExtSign Sign.Sign Symbol.Symbol, 
             [AS_Anno.Named (CL.SENTENCE)])
basicCommonLogicAnalysis (bs, sig, _) = 
   Result.Result [] $ if exErrs then Nothing else 
     Just (bs, ExtSign sigItems newSyms, sentences) 
    where
      -- bsig      = bs sig
      sigItems  = sig
      newSyms   = Set.map Symbol.Symbol 
        $ Set.difference (items sigItems) $ items sig
      bsform    = makeFormulas bs sigItems -- [DIAG_FORM] list of sentence
      sentences = map formula bsform
      exErrs    = False
