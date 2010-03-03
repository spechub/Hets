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


module Reduce.Analysis
    (
     splitSpec
     ,basicReduceAnalysis
--     basicReduceAnalysis
--    ,mkStatSymbItems
--    ,mkStatSymbMapItem
--   ,inducedFromMorphism
--    ,inducedFromToMorphism
--    , signatureColimit
    )
    where

import Common.ExtSign
import Reduce.Sign as Sign
import qualified Common.AS_Annotation as AS_Anno
import Common.Id
import Common.Result
import qualified Data.List as List
import qualified Data.Set as Set
import Reduce.AS_BASIC_Reduce 
import Reduce.Symbol 


-- | Datatype for formulas with diagnosis data
data DIAG_FORM = DiagForm
    {
      formula :: (AS_Anno.Named CMD),
      diagnosis :: Diagnosis
    }
               deriving Show

-- | extracts the operators of a given Expression, will be used for analysis
-- extractOperators :: EXPRESSION -> [String]
-- extractOperators (Op s exps _) = s:(concat (map extractOperators exps))
-- extractOperators (List exps _) = (concat (map extractOperators exps))
-- extractOperators _ = []


-- | generates a named formula
makeNamed :: AS_Anno.Annoted CMD -> Int -> AS_Anno.Named CMD
makeNamed f i = (AS_Anno.makeNamed (if label == "" then "Ax_" ++ show i
                                       else label) $ AS_Anno.item f)
                    { AS_Anno.isAxiom = not isTheorem }
    where
      label = AS_Anno.getRLabel f
      annos = AS_Anno.r_annos f
      isImplies = foldl (\y x -> AS_Anno.isImplies x || y) False annos
      isImplied = foldl (\y x -> AS_Anno.isImplied x || y) False annos
      isTheorem = isImplies || isImplied


-- | takes a signature and a formula, analyzes it and returns a formula with diagnosis
analyzeFormula :: Sign.Sign -> (AS_Anno.Annoted CMD) -> Int -> DIAG_FORM
analyzeFormula _ f i = DiagForm { formula = (makeNamed f i), 
                                             diagnosis = Diag {
                                               diagKind = Hint
                                             , diagString = "All fine"
                                             , diagPos    = nullRange
                                                         }
                                 }

-- | Extracts the axioms and the signature of a basic spec
splitSpec :: BASIC_SPEC -> Sign.Sign -> (Sign.Sign,[DIAG_FORM])
splitSpec (Basic_spec specitems) sig =
    List.foldl (\(sign,axs) item -> 
                case (AS_Anno.item item) of
                  (Op_decl (Op_item tokens _)) -> (addTokens sign tokens,axs) 
                  (Axiom_item annocmd) -> (sign,(analyzeFormula sign annocmd (length axs)):axs) --  addAxioms cmds sign
                 )
             (sig,[]) specitems

-- | adds the specified tokens to the signature
addTokens :: Sign.Sign -> [Token] -> Sign.Sign
addTokens sign tokens = foldl (\res item -> (addToSig res (simpleIdToId item))) sign tokens


-- | stepwise extends an initially empty signature by the basic spec bs. The resulting spec contains analyzed axioms in it. 
-- The result contains: 1) the basic spec 2) the new signature + the added symbols 3) sentences of the spec 
basicReduceAnalysis :: (BASIC_SPEC, Sign, a) -> Result (BASIC_SPEC, ExtSign Sign Symbol, [AS_Anno.Named CMD])
basicReduceAnalysis (bs, sig, _) =
    Result diagnoses $ if exErrs then Nothing else
                       Just (bs, ExtSign newSig newSyms, (map formula cmds))
        where
          (newSig,cmds)     = splitSpec bs sig
          diagnoses     = []
          exErrs    = False
          newSyms   = Set.map Symbol $ Set.difference (items newSig) $ items sig


