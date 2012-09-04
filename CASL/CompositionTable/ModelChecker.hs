{- |
Module      :  $Header$
Description :  checks validity of models regarding a composition table
Copyright   :  (c) Uni Bremen 2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  fmossa@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable

checks validity of models regarding a composition table
-}

module CASL.CompositionTable.ModelChecker where

import CASL.CompositionTable.CompositionTable
import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.ToDoc
import CASL.Logic_CASL
import Logic.Logic

import Common.AS_Annotation
import Common.Result
import Common.Id
import Common.DocUtils
import qualified Common.Lib.MapSet as MapSet

import qualified Data.Set as Set
import Data.Maybe
import Data.List

modelCheck :: Int -> (Sign () (), [Named (FORMULA ())])
           -> Table -> Result Bool
modelCheck _ (_, []) _ = justWarn True "not implemented"
modelCheck c (sign, sent) t =
    modelCheckTest c (extractAnnotations (annoMap sign)) (sign, sent) t

extractAnnotations :: MapSet.MapSet Symbol Annotation -> [(OP_SYMB, String)]
extractAnnotations m =
    catMaybes [extractAnnotation (a, b) | (a, b) <- MapSet.toList m]

extractAnnotation :: (Symbol, [Annotation]) -> Maybe (OP_SYMB, String)
extractAnnotation (Symbol symbname symbtype, set) = case symbtype of
    OpAsItemType _ -> Just (createOpSymb symbname symbtype, getAnno set)
    _ -> Nothing

createOpSymb :: Id -> SymbType -> OP_SYMB
createOpSymb i st = case st of
  OpAsItemType ty -> Qual_op_name i (toOP_TYPE ty) nullRange
  _ -> error "CASL.CompositionTable.ModelChecker.createOpSymb"

getAnno :: [Annotation] -> String
getAnno as = case as of
   [a] -> getAnnoAux a
   _ -> "failure"

getAnnoAux :: Annotation -> String
getAnnoAux a = case a of
    Unparsed_anno (Annote_word word) _ _ -> word
    _ -> ""

showDiagStrings :: [Diagnosis] -> String
showDiagStrings = intercalate "\n" . map diagString

modelCheckTest :: Int -> [(OP_SYMB, String)]
  -> (Sign () (), [Named (FORMULA ())]) -> Table -> Result Bool
modelCheckTest _ _ (_, []) _ =
 error "CASL.CompositionTable.ModelChecker.modelCheckTest"
modelCheckTest c symbs (sign, xs) t = case xs of
  [] -> error "CASL.CompositionTable.ModelChecker.modelCheckTest"
  [x] -> let
    Result d _ = modelCheckTest1 (sign, x) t symbs
    n = length d
    fstr = shows (printTheoryFormula (mapNamed (simplify_sen CASL sign) x)) "\n"
      in if null d
      then hint True ("Formula succeeded:\n" ++ fstr) nullRange
      else warning False ("Formula failed:\n" ++ fstr ++ show n
               ++ " counter example" ++ (if n > 1 then "s" else "")
               ++ ":\n" ++ showDiagStrings (take c d)) nullRange
  x : r -> do
    modelCheckTest c symbs (sign, r) t
    modelCheckTest c symbs (sign, [x]) t

modelCheckTest1 :: (Sign () (), Named (FORMULA ())) -> Table
                -> [(OP_SYMB, String)] -> Result Bool
modelCheckTest1 (sign, nSen) t symbs = case sentence nSen of
    Junction j formulas range -> let
        varass = Variable_Assignment []
        bs = map (\ f -> calculateFormula (sign, f) varass t symbs)
             formulas
        res = if j == Con then and else or
        in if res bs then return True else
            warning False (show j ++ "junction does not hold:"
                                 ++ showDoc (map (simplify_sen CASL sign)
                                 formulas) "") range
    f@(Relation f1 c f2 range) ->
                  let varass = Variable_Assignment []
                      test1 = calculateFormula (sign, f1) varass t symbs
                      test2 = calculateFormula (sign, f2) varass t symbs
                      res = not (test1 && not test2)
                  in if if c == Equivalence then test1 == test2 else res
                     then return True
                     else warning False ("Relation does not hold: " ++
                          showDoc (simplify_sen CASL sign f) "") range
    Negation f range ->
                  let varass = Variable_Assignment []
                      res = calculateFormula (sign, f) varass t symbs
                  in if not res then return True
                    else warning False
                                        ("Negation does not hold:"
                                        ++ showDoc (simplify_sen CASL
                                                   sign f) "") range
    Atom b range -> if b then return True else
      warning False "False-atom can't be fulfilled!" range
    Equation t1 Strong t2 range ->
                  let varass = Variable_Assignment []
                      res1 = calculateTerm (sign, t1) varass t symbs
                      res2 = calculateTerm (sign, t2) varass t symbs
                      equal = equalElements res1 res2
                  in if equal then return True
                     else warning False
                       ("Strong Equation does not hold term1: "
                        ++ showDoc t1 "term2: " ++ showDoc t2 "") range
    qf@(Quantification _ decl _ _) ->
        let ass = generateVariableAssignments decl t
        in calculateQuantification (sign, qf)
                  ass t symbs
    e -> error $ "CASL.CompositionTable.ModelChecker.modelCheckTest1 "
         ++ showDoc e ""

calculateQuantification :: (Sign () (), FORMULA ()) -> [VARIABLE_ASSIGNMENT]
                        -> Table -> [(OP_SYMB, String)] -> Result Bool
calculateQuantification (sign, qf) vardecls t symbs = case qf of
    Quantification quant _ f range ->
        let tuples = map ( \ ass -> let
                res = calculateFormula (sign, f) ass t symbs
                in if res then (res, "") else (res, ' ' : show ass))
              vardecls
        in case quant of
        Universal -> let failedtuples = filter (not . fst) tuples
          in if null failedtuples then return True else do
             mapM_ (\ (_, msg) -> warning () msg range) failedtuples
             return False
        Existential -> let suceededTuples = filter fst tuples
          in if not (null suceededTuples) then return True else
               warning False "Existential not fulfilled" range
        Unique_existential ->
          let suceededTuples = take 2 $ filter fst tuples in
          case suceededTuples of
            [_] -> return True
            _ -> warning False "Unique Existential not fulifilled" range
    _ -> error "CASL.CompositionTable.ModelChecker.calculateQuantification"

data VARIABLE_ASSIGNMENT = Variable_Assignment [(VAR, Baserel)]

instance Show VARIABLE_ASSIGNMENT where
    show (Variable_Assignment assignList) = showAssignments assignList

showAssignments :: [(VAR, Baserel)] -> String
showAssignments xs =
    '[' : intercalate ", " (map showSingleAssignment xs) ++ "]"

showSingleAssignment :: (VAR, Baserel) -> String
showSingleAssignment (v, Baserel b) = show v ++ "->" ++ b

concatAssignment :: VARIABLE_ASSIGNMENT -> VARIABLE_ASSIGNMENT
                 -> VARIABLE_ASSIGNMENT
concatAssignment (Variable_Assignment l1) (Variable_Assignment l2) =
  Variable_Assignment $ l1 ++ l2

calculateTerm :: (Sign () (), TERM ()) -> VARIABLE_ASSIGNMENT -> Table
              -> [(OP_SYMB, String)] -> [Baserel]
calculateTerm (sign, trm) ass t symbs = case trm of
    Qual_var var _ _ -> getBaseRelForVariable var ass
    Application opSymb terms _ ->
              applyOperation (getIdentifierForSymb opSymb symbs) (sign, terms)
              t ass symbs
    Sorted_term term _ _ -> calculateTerm (sign, term) ass t symbs
    Cast {} -> error "CASL.CompositionTable.ModelChecker.calculateTerm"
    Conditional t1 fo t2 _ ->
              let res = calculateFormula (sign, fo) ass t symbs
              in if res then calculateTerm (sign, t1) ass t symbs
                 else calculateTerm (sign, t2) ass t symbs
    _ -> []

getIdentifierForSymb :: OP_SYMB -> [(OP_SYMB, String)] -> String
getIdentifierForSymb symb = concatMap (getIdentifierForSymbAtomar symb)

getIdentifierForSymbAtomar :: OP_SYMB -> (OP_SYMB, String) -> String
getIdentifierForSymbAtomar symb (symb2, s) = if symb == symb2 then s else ""

applyOperation :: String -> (Sign () (), [TERM ()]) -> Table
               -> VARIABLE_ASSIGNMENT -> [(OP_SYMB, String)] -> [Baserel]
applyOperation "RA_zero" (_, []) _ _ _ = []
applyOperation "RA_one" _ (Table (Table_Attrs _ _ baserels)
              _ _ _ _) _ _ = baserels
applyOperation "RA_intersection" (sign, ft : sd : _) table ass symbs = intersect
              (calculateTerm (sign, ft) ass table symbs)
              (calculateTerm (sign, sd) ass table symbs)
applyOperation "RA_composition" (sign, ft : sd : _) (Table attrs
              (Compositiontable cmpentries) convtbl refltbl models)
              ass symbs = calculateComposition cmpentries
              (calculateTerm (sign, ft) ass (Table attrs
              (Compositiontable cmpentries) convtbl refltbl models) symbs)
              (calculateTerm (sign, sd) ass (Table attrs
              (Compositiontable cmpentries) convtbl refltbl models) symbs)
applyOperation "RA_union" (sign, ft : sd : _) table ass symbs = union
              (calculateTerm (sign, ft) ass table symbs)
              (calculateTerm (sign, sd) ass table symbs)
applyOperation "RA_complement" (sign, ft : _) (Table (Table_Attrs name id_
               baserels) comptbl convtbl refltbl models) ass symbs =
               complement
               (calculateTerm (sign, ft) ass (Table (Table_Attrs
               name id_ baserels) comptbl convtbl refltbl models)
               symbs) baserels
applyOperation "RA_identity" _ (Table (Table_Attrs _ id_ _)
               _ _ _ _) _ _ = [id_]
applyOperation "RA_converse" (sign, ft : _)
    (Table attrs cmptable cnvtable refltbl models) ass symbs =
  calculateConverse cnvtable
    (calculateTerm (sign, ft) ass
     (Table attrs cmptable cnvtable refltbl models) symbs)

applyOperation "RA_shortcut" (sign, ft : _) (Table attrs comptbl
                (Conversetable_Ternary inv shortc hom) refltbl
                models) ass symbs = calculateConverseTernary shortc
                (calculateTerm (sign, ft) ass (Table attrs comptbl
                (Conversetable_Ternary inv shortc hom) refltbl
                models) symbs)
applyOperation "RA_inverse" (sign, ft : _) (Table attrs comptbl
                (Conversetable_Ternary inv shortc hom) refltbl
                models) ass symbs = calculateConverseTernary inv
                (calculateTerm (sign, ft) ass (Table attrs comptbl
                (Conversetable_Ternary inv shortc hom) refltbl
                models) symbs)

applyOperation "RA_homing" (sign, ft : _) (Table attrs comptbl
                (Conversetable_Ternary inv shortc hom) refltbl
                models) ass symbs = calculateConverseTernary hom
                (calculateTerm (sign, ft) ass (Table attrs comptbl
                (Conversetable_Ternary inv shortc hom) refltbl
                models) symbs)
applyOperation _ _ _ _ _ = []

complement :: [Baserel] -> [Baserel] -> [Baserel]
complement rels baserles = baserles \\ rels

calculateComposition :: [Cmptabentry] -> [Baserel] -> [Baserel] -> [Baserel]
calculateComposition entries rels1 rels2 =
    concatMap (calculateCompositionAux rels1 rels2) entries

calculateCompositionAux :: [Baserel] -> [Baserel] -> Cmptabentry -> [Baserel]
calculateCompositionAux rels1 rels2
    (Cmptabentry (Cmptabentry_Attrs rel1 rel2) baserels) =
  if elem rel1 rels1 && elem rel2 rels2 then baserels else []

calculateConverse :: Conversetable -> [Baserel] -> [Baserel]
calculateConverse (Conversetable_Ternary {}) _ = []
calculateConverse (Conversetable centries) rels =
    concatMap (calculateConverseAtomar rels) centries

calculateConverseAtomar :: [Baserel] -> Contabentry -> [Baserel]
calculateConverseAtomar rels (Contabentry rel1 rel2) =
   [rel2 | elem rel1 rels]

calculateConverseTernary :: [Contabentry_Ternary] -> [Baserel]
                         -> [Baserel]
calculateConverseTernary entries rels =
    concatMap (calculateConverseTernaryAtomar rels) entries

calculateConverseTernaryAtomar :: [Baserel] -> Contabentry_Ternary -> [Baserel]
calculateConverseTernaryAtomar rels2 (Contabentry_Ternary rel1 rels1) =
  if elem rel1 rels2 then rels1 else []

getBaseRelForVariable :: VAR -> VARIABLE_ASSIGNMENT -> [Baserel]
getBaseRelForVariable var (Variable_Assignment tuples) =
    concatMap (getBaseRelForVariableAtomar var) tuples

getBaseRelForVariableAtomar :: VAR -> (VAR, Baserel) -> [Baserel]
getBaseRelForVariableAtomar v (var, baserel) = [baserel | v == var]

calculateFormula :: (Sign () (), FORMULA ()) -> VARIABLE_ASSIGNMENT -> Table
                 -> [(OP_SYMB, String)] -> Bool
calculateFormula (sign, qf) varass t symbs = case qf of
    Quantification _ vardecls _ _ ->
                 let (Result _ res) = (calculateQuantification (sign, qf)
                                       (appendVariableAssignments
                                       varass vardecls t) t symbs)
                 in res == Just True
    Junction j formulas _ -> (if j == Con then and else or)
        [calculateFormula (sign, x) varass t symbs | x <- formulas]
    Relation f1 c f2 _ ->
                 let test1 = calculateFormula (sign, f1) varass t symbs
                     test2 = calculateFormula (sign, f2) varass t symbs
                 in if c == Equivalence then test1 == test2 else
                        not (test1 && not test2)
    Negation f _ -> not (calculateFormula (sign, f) varass t symbs)
    Atom b _ -> b
    Equation term1 Strong term2 _ ->
                 let t1 = calculateTerm (sign, term1) varass t symbs
                     t2 = calculateTerm (sign, term2) varass t symbs
                 in equalElements t1 t2
    _ -> error $ "CASL.CompositionTable.ModelChecker.calculateFormula "
         ++ showDoc qf ""

equalElements :: [Baserel] -> [Baserel] -> Bool
equalElements a b = Set.toList (Set.fromList a) == Set.toList (Set.fromList b)

generateVariableAssignments :: [VAR_DECL] -> Table -> [VARIABLE_ASSIGNMENT]
generateVariableAssignments vardecls t =
    map Variable_Assignment (gVAs (getVars vardecls) (getBaseRelations t))

gVAs :: [VAR] -> [Baserel] -> [[(VAR, Baserel)]]
gVAs [] _ = [[]]
gVAs (v : vs) baserels = let
    rs = gVAs vs baserels
    fs = map (\ b -> [(v, b)]) baserels
    in [f ++ r | f <- fs, r <- rs]

appendAssignments :: [[(VAR, Baserel)]] -> [VAR] -> [Baserel]
                  -> [[(VAR, Baserel)]]
appendAssignments _ _ [] = []
appendAssignments tuples [] _ = tuples
appendAssignments tuples (x : xs) baserels = appendAssignments
                                           (appendAssignmentsAux tuples x
                                           baserels) xs
                                           baserels

appendAssignmentsAux :: [[(VAR, Baserel)]] -> VAR -> [Baserel]
                     -> [[(VAR, Baserel)]]
appendAssignmentsAux [] var baserels = appendAssignmentSingle var baserels []
appendAssignmentsAux list var baserels =
    concatMap (appendAssignmentSingle var baserels) list

appendAssignmentSingle :: VAR -> [Baserel] -> [(VAR, Baserel)]
                       -> [[(VAR, Baserel)]]
appendAssignmentSingle var rels assignment = map (appendAssignmentSingle1
                                                  assignment var) rels

appendAssignmentSingle1 :: [(VAR, Baserel)] -> VAR -> Baserel
                        -> [(VAR, Baserel)]
appendAssignmentSingle1 acc var rel = (var, rel) : acc

getVars :: [VAR_DECL] -> [VAR]
getVars = concatMap getVarsAtomic

getVarsAtomic :: VAR_DECL -> [VAR]
getVarsAtomic (Var_decl vars _ _) = vars

getBaseRelations :: Table -> [Baserel]
getBaseRelations (Table (Table_Attrs _ _ br) _ _ _ _) = br

appendVariableAssignments :: VARIABLE_ASSIGNMENT -> [VAR_DECL] -> Table
                          -> [VARIABLE_ASSIGNMENT]
appendVariableAssignments vars decls t =
     map (concatAssignment vars) (generateVariableAssignments decls t)
