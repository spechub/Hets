{- |
Module      :  $Header$
Description :  Abstract syntax for reduce
Copyright   :  (c) Dominik Dietrich, DFKI Bremen 2010
License     :  GPLv2 or higher

Maintainer  :  dominik.dietrich@dfki.de
Stability   :  experimental
Portability :  portable

-}

-- todo: add static analysis for repeat

module CSL.Analysis
    ( splitSpec
    , basicCSLAnalysis
    , arityOneOps, arityTwoOps, arityFlexOps
-- basicCSLAnalysis
-- ,mkStatSymbItems
-- ,mkStatSymbMapItem
-- ,inducedFromMorphism
-- ,inducedFromToMorphism
-- , signatureColimit
    )
    where

import Common.ExtSign
import CSL.Sign as Sign
import qualified Common.AS_Annotation as AS_Anno
import Common.Id
import Common.Result
import qualified Data.Set as Set
import qualified Data.Map as Map
import CSL.AS_BASIC_CSL
import CSL.Symbol


-- * Diagnosis Types and Functions

-- | Datatype for formulas with diagnosis data
data DIAG_FORM = DiagForm
    {
      formula :: (AS_Anno.Named CMD),
      diagnosis :: Diagnosis
    } deriving Show

arityOneOps :: [String]
arityOneOps = [ "cos", "sin", "tan", "sqrt", "fthrt", "--", "abs"
              , "simplify", "rlqe", "factorize"
              ]

arityTwoOps :: [String]
arityTwoOps = [ "ex", "all", "and", "or", "impl"
              , "=", ">", "<=", ">=", "!=", "<"
              , "+", "*", "/", "**", "^"
              , ":=", "int", "divide", "solve"
              ]

arityFlexOps :: [String]
arityFlexOps = [ "min", "max", "-" ]

-- | extracts the operators + arity information for an operator
extractOperatorsExp :: EXPRESSION -> [(String,Int)]
extractOperatorsExp (Var _) = []
extractOperatorsExp (Op s _ exps _) =
    (s, length exps) : concatMap extractOperatorsExp exps
extractOperatorsExp (List exps _) = concatMap extractOperatorsExp exps
extractOperatorsExp _ = []

-- | extracts the operators + arity information for a cmd
extractOperatorsCmd :: CMD -> [(String,Int)]
extractOperatorsCmd (Cmd cmd exps) =
    (cmd, length exps) : concatMap extractOperatorsExp exps
extractOperatorsCmd (Repeat _ _) = [] -- TODO: to be implemented
extractOperatorsCmd (Cond _) = [] -- TODO: to be implemented

-- | checks whether the command is correctly declared 
checkOperators :: Sign.Sign -> [(String,Int)] -> Bool
checkOperators _ ops =
    let f (op, arit) =
            case Map.lookup op operatorInfo of
              Just oim ->
                  -- it must be registered with the given arity or as flex-op
                  Map.member arit oim || Map.member (-1) oim
              -- if not registered we accept it
              _ -> True
    in all f ops

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


-- | takes a signature and a formula and a number. 
-- It analyzes the formula and returns a formula with diagnosis
analyzeFormula :: Sign.Sign -> (AS_Anno.Annoted CMD) -> Int -> DIAG_FORM
analyzeFormula s f i
    | checkOperators s $ extractOperatorsCmd $ AS_Anno.item f
        = DiagForm { formula = (makeNamed f i),
                               diagnosis = Diag {
                                             diagKind = Hint
                                           , diagString = "All fine"
                                           , diagPos = nullRange
                                           }
                   }
    | otherwise
        = let ds = "Wrong arity or undeclared operator in Formula "
                   ++ show (extractOperatorsCmd (AS_Anno.item f)) ++ " "
                   ++ show (AS_Anno.item f)
          in  DiagForm { formula = (makeNamed f i),
                                   diagnosis = Diag {
                                                 diagKind = Error
                                               , diagString = ds
                                               -- position of the error
                                               , diagPos = nullRange
                                               }
                       }

-- | Extracts the axioms and the signature of a basic spec
splitSpec :: BASIC_SPEC -> Sign.Sign -> (Sign.Sign, [DIAG_FORM])
splitSpec (Basic_spec specitems) sig =
    -- use foldr here, foldl would switch the order of the sentences
    foldr (\ item bs@(sign, axs) ->
               case (AS_Anno.item item) of
                 Op_decl (Op_item tokens _) ->
                     (addTokens sign tokens, axs)
                 Var_decls _ -> bs -- TODO: implement
                 Axiom_item annocmd ->
                     -- addAxioms cmds sign
                     (sign, (analyzeFormula sign annocmd (length axs)) : axs)
          ) (sig, []) specitems

-- | adds the specified tokens to the signature
addTokens :: Sign.Sign -> [Token] -> Sign.Sign
addTokens sign tokens = foldl (\ res item -> (addToSig res (simpleIdToId item))) sign tokens


-- | stepwise extends an initially empty signature by the basic spec bs. The resulting spec contains analyzed axioms in it.
-- The result contains: 1) the basic spec 2) the new signature + the added symbols 3) sentences of the spec
basicCSLAnalysis :: (BASIC_SPEC, Sign, a)
                 -> Result (BASIC_SPEC, ExtSign Sign Symbol, [AS_Anno.Named CMD])
basicCSLAnalysis (bs, sig, _) =
    Result diagnoses $ if exErrs then Nothing else
                       Just (bs, ExtSign newSig newSyms, (map formula diagcmds))
        where
          (newSig, diagcmds) = splitSpec bs sig
          diagnoses = (map diagnosis diagcmds)
          exErrs = False
          newSyms = Set.map Symbol $ Set.difference (items newSig) $ items sig
