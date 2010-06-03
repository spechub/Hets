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

-- todo: add static analysis for repeat

module Reduce.Analysis
    (
     splitSpec
     , basicReduceAnalysis
-- basicReduceAnalysis
-- ,mkStatSymbItems
-- ,mkStatSymbMapItem
-- ,inducedFromMorphism
-- ,inducedFromToMorphism
-- , signatureColimit
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

-- | extracts the operators + arity information for an operator
extractOperatorsExp :: EXPRESSION -> [(String,Int)]
extractOperatorsExp (Var _) = []
extractOperatorsExp (Op s exps _) = (s,(length exps)) : (List.foldl (\ res item -> (res ++ (extractOperatorsExp item)) ) [] exps)
extractOperatorsExp (List exps _) = (List.foldl (\ res item -> (res ++ (extractOperatorsExp item)) ) [] exps)
extractOperatorsExp _ = []

-- | extracts the operators + arity information for a cmd
extractOperatorsCmd :: CMD -> [(String,Int)]
extractOperatorsCmd (Cmd cmd exps) = (cmd,length exps) : (List.foldl (\ res item -> (res ++ (extractOperatorsExp item)) ) [] exps)
extractOperatorsCmd (Repeat _ _ _) = [] -- to be implemented

-- | checks whether the command is correctly declared 
checkOperators :: Sign.Sign -> [(String,Int)] -> Bool
checkOperators _ [] = True
checkOperators s ((op,arit):ops) = (if elem op ["ex","all",">","<=",">=","!=","<","+","-","*","=","/","**","^","and","or","impl"] then (arit==2)
                                    else if elem op ["cos","sqrt","sin"] then (arit==1) else
                                        case op of
                                          "solve" -> (arit==2)
                                          "simplify" -> (arit==1)
                                          "divide" -> (arit==2)
                                          "int" -> (arit==2)
                                          "rlqe" -> (arit==1)
                                          ":="   -> (arit==2)
                                          "factorize" -> (arit==1)
                                          "min" -> (arit>0)
                                          "max" -> (arit>0)
                                          _ -> Sign.lookupSym s $ genName op  -- .. otherwise it must be declared in the signature
                                               )
                                   && checkOperators s ops

-- | generates a named formula
makeNamed :: AS_Anno.Annoted CMD -> Int -> AS_Anno.Named CMD
makeNamed f i = (AS_Anno.makeNamed (if label == "" then "Ax_" ++ show i
                                       else label) $ AS_Anno.item f)
                    { AS_Anno.isAxiom = not isTheorem }
    where
      label = AS_Anno.getRLabel f
      annos = AS_Anno.r_annos f
      isImplies = foldl (\ y x -> AS_Anno.isImplies x || y) False annos
      isImplied = foldl (\ y x -> AS_Anno.isImplied x || y) False annos
      isTheorem = isImplies || isImplied


-- | takes a signature and a formula and a number. It analyzes the formula and returns a formula with diagnosis
analyzeFormula :: Sign.Sign -> (AS_Anno.Annoted CMD) -> Int -> DIAG_FORM
analyzeFormula s f i =  
    let
        opargs = extractOperatorsCmd (AS_Anno.item f)
    in
      if (checkOperators s opargs) then 
          DiagForm { formula = (makeNamed f i),
                               diagnosis = Diag {
                                             diagKind = Hint
                                           , diagString = "All fine"
                                           , diagPos = nullRange
                                           }
                   }
          else
          DiagForm { formula = (makeNamed f i),
                               diagnosis = Diag {
                                             diagKind = Error
                                           , diagString = "Wrong arity or undeclared operator in Formula " ++ show (extractOperatorsCmd (AS_Anno.item f)) ++ " " ++ show (AS_Anno.item f)
                                           , diagPos = nullRange -- position of the error
                                           }
                   }

-- | Extracts the axioms and the signature of a basic spec
splitSpec :: BASIC_SPEC -> Sign.Sign -> (Sign.Sign, [DIAG_FORM])
splitSpec (Basic_spec specitems) sig =
    List.foldl (\ (sign, axs) item ->
                case (AS_Anno.item item) of
                  (Op_decl (Op_item tokens _)) -> (addTokens sign tokens, axs)
                  (Axiom_item annocmd) -> (sign, (analyzeFormula sign annocmd (length axs)) : axs) -- addAxioms cmds sign
                 )
             (sig, []) specitems

-- | adds the specified tokens to the signature
addTokens :: Sign.Sign -> [Token] -> Sign.Sign
addTokens sign tokens = foldl (\ res item -> (addToSig res (simpleIdToId item))) sign tokens


-- | stepwise extends an initially empty signature by the basic spec bs. The resulting spec contains analyzed axioms in it.
-- The result contains: 1) the basic spec 2) the new signature + the added symbols 3) sentences of the spec
basicReduceAnalysis :: (BASIC_SPEC, Sign, a) -> Result (BASIC_SPEC, ExtSign Sign Symbol, [AS_Anno.Named CMD])
basicReduceAnalysis (bs, sig, _) =
    Result diagnoses $ if exErrs then Nothing else
                       Just (bs, ExtSign newSig newSyms, (map formula diagcmds))
        where
          (newSig, diagcmds) = splitSpec bs sig
          diagnoses = (map diagnosis diagcmds)
          exErrs = False
          newSyms = Set.map Symbol $ Set.difference (items newSig) $ items sig
