{- |
Module      :  $Header$
Description :  checks validity of models regarding a composition table
Copyright   :  (c) Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

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

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe
import Data.List
import Control.Monad

modelCheck :: SIMPLE_ID -> (Sign () (), [Named (FORMULA ())])
           -> Table -> Result Bool
modelCheck _ (_, []) _ = (warning True "not implemented" nullRange)
modelCheck _ (sign, sent) t =
    modelCheckTest (extractAnnotations (annoMap sign)) (sign, sent) t

extractAnnotations :: Map.Map Symbol (Set.Set Annotation)
                   -> [(OP_SYMB, String)]
extractAnnotations m =
    catMaybes [extractAnnotation (a, b) | (a, b) <- Map.toList m]

extractAnnotation :: (Symbol, Set.Set Annotation) -> Maybe (OP_SYMB, String)
extractAnnotation (Symbol symbname symbtype, set) = case symbtype of
    OpAsItemType _ -> Just (createOpSymb symbname symbtype, getAnno set)
    PredAsItemType _ -> Nothing
    SortAsItemType -> Nothing

createOpSymb :: Id -> SymbType -> OP_SYMB
createOpSymb i st = case st of
  OpAsItemType ty -> Qual_op_name i (toOP_TYPE ty) nullRange
  _ -> error "CASL.CompositionTable.ModelChecker.createOpSymb"

getAnno :: Set.Set Annotation -> String
getAnno a
 | Set.size a == 1 = getAnnoAux (Set.findMin a)
 | otherwise = "failure"

getAnnoAux :: Annotation -> String
getAnnoAux a = case a of
    Unparsed_anno (Annote_word word) _ _ -> word
    _ -> ""

showDiagStrings:: [Diagnosis] -> [Char]
showDiagStrings = concat . intersperse "\n" . map diagString

modelCheckTest ::  [(OP_SYMB, String)] -> (Sign () (), [Named (FORMULA ())])
               -> Table -> Result Bool
modelCheckTest _ (_, []) _ =
 error "CASL.CompositionTable.ModelChecker.modelCheckTest"
modelCheckTest symbs (sign, xs) t = case xs of
  [] -> error "CASL.CompositionTable.ModelChecker.modelCheckTest"
  [x] -> let
    Result d _ = modelCheckTest1 (sign, x) t symbs
    fstr = shows(printTheoryFormula(mapNamed (simplify_sen CASL sign) x)) "\n"
      in if null d
      then hint True ("Formula succeeded: " ++ fstr)  nullRange
      else warning False ("Formula failed: \n" ++ fstr ++
               " some Counterexamples: \n"
               ++ showDiagStrings(take 10 d)) nullRange
  x : r -> do
    modelCheckTest symbs (sign, r) t
    modelCheckTest symbs (sign, [x]) t

modelCheckTest1 :: (Sign () (), Named (FORMULA ())) -> Table
                -> [(OP_SYMB,String)] -> Result Bool
modelCheckTest1 (sign, nSen) t symbs = case sentence nSen of
    Conjunction formulas range -> let
        varass = Variable_Assignment []
        res = and [ calculateFormula (sign, formula) varass t symbs
                  | formula <- formulas ]
        in if res then return True
           else warning False ("Conjunction does not hold:"
                                 ++ showDoc(map (simplify_sen CASL sign)
                                 formulas) "") range
    Disjunction formulas range -> let
        varass = Variable_Assignment []
        res = or [ calculateFormula (sign, formula) varass t symbs
                 | formula <- formulas ]
        in if res then return True
           else warning False ("Disjunction does not hold:"
                                  ++ showDoc((map (simplify_sen
                                  CASL sign) formulas)) "") range
    Implication f1 f2 _ range ->
                  let varass = Variable_Assignment []
                      test1 = calculateFormula (sign, f1) varass t symbs
                      test2 = calculateFormula (sign, f2) varass t symbs
                      res = not (test1 && not test2)
                  in if res then return True
                     else warning False ("Implication does not hold: f1 is" ++
                          showDoc(simplify_sen CASL sign f1) "" ++ "f2 is " ++
                          showDoc(simplify_sen CASL sign f2) "") range
    Equivalence f1 f2 range ->
                  let varass = Variable_Assignment []
                      test1 = calculateFormula (sign, f1) varass t symbs
                      test2 = calculateFormula (sign, f2) varass t symbs
                      res = test1 == test2
                 in  if res then return True
                     else warning False ("Equivalence does not hold: f1 is"
                           ++ showDoc (simplify_sen CASL sign f1) "" ++
                           "f2 is " ++ showDoc (simplify_sen CASL sign f2) "")
                           range
    Negation f range ->
                  let varass = Variable_Assignment []
                      res = calculateFormula (sign,f) varass t symbs
                  in if not res then return True
                    else warning False
                                        ("Negation does not hold:"
                                        ++ showDoc(simplify_sen CASL
                                                   sign f) "") range
    True_atom _ -> return True
    False_atom range -> warning False "False-atom can't be fulfilled!" range
    Strong_equation t1 t2 range ->
                  let varass = Variable_Assignment []
                      res1 = calculateTerm (sign,t1) varass t symbs
                      res2 = calculateTerm (sign,t2) varass t symbs
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
                in if res then (res, "") else (res, " " ++ show ass))
              vardecls
        in case quant of
        Universal -> let failedtuples = take 10 $ filter (not.fst) tuples
          in if null failedtuples then return True else do
             mapM_ (\ (_, msg)-> warning () msg range) failedtuples
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

data VARIABLE_ASSIGNMENT = Variable_Assignment [(VAR, Baserel)] deriving Eq

instance Show VARIABLE_ASSIGNMENT where
    show (Variable_Assignment assignList) = showAssignments assignList

showAssignments :: [(VAR, Baserel)] -> String
showAssignments xs =
    "["++ concat (intersperse ", " $ map showSingleAssignment xs)  ++"]"

showSingleAssignment :: (VAR, Baserel) -> String
showSingleAssignment (v, Baserel b) = show v ++ "->" ++ b

concatAssignment :: VARIABLE_ASSIGNMENT -> VARIABLE_ASSIGNMENT
                 -> VARIABLE_ASSIGNMENT
concatAssignment (Variable_Assignment l1) (Variable_Assignment l2) =
  Variable_Assignment $ l1 ++ l2

calculateTerm :: (Sign () (), TERM ()) -> VARIABLE_ASSIGNMENT -> Table
              -> [(OP_SYMB,String)] -> [Baserel]
calculateTerm (sign, trm) ass t symbs = case trm of
    Qual_var var _ _ -> getBaseRelForVariable var ass
    Application opSymb terms _ ->
              applyOperation (getIdentifierForSymb opSymb symbs) (sign, terms)
              t ass symbs
    Sorted_term term _ _ -> calculateTerm (sign, term) ass t symbs
    Cast _ _ _ -> error "CASL.CompositionTable.ModelChecker.calculateTerm"
    Conditional t1 fo t2 _ ->
              let res = calculateFormula (sign, fo) ass t symbs
              in if res then calculateTerm (sign, t1) ass t symbs
                 else calculateTerm (sign, t2) ass t symbs
    _ -> []

getIdentifierForSymb :: OP_SYMB -> [(OP_SYMB, String)] -> String
getIdentifierForSymb symb = concatMap (getIdentifierForSymbAtomar symb)

getIdentifierForSymbAtomar :: OP_SYMB -> (OP_SYMB, String) -> String
getIdentifierForSymbAtomar symb (symb2, s) = if symb == symb2 then s else ""

applyOperation :: String -> (Sign () (), [(TERM ())]) -> Table
               -> VARIABLE_ASSIGNMENT -> [(OP_SYMB,String)]-> [Baserel]
applyOperation "RA_zero" (_, []) _ _ _ = []
applyOperation "RA_one" _ (Table (Table_Attrs _ _ baserels)
              _ _ _ _) _ _ = baserels
applyOperation "RA_intersection" (sign,terms) table ass symbs = intersect
              (calculateTerm (sign,(head terms)) ass table symbs)
              (calculateTerm (sign,(head (tail terms))) ass table symbs)
applyOperation "RA_composition" (sign,terms) (Table attrs
              (Compositiontable cmpentries) convtbl refltbl models)
              ass symbs = calculateComposition cmpentries
              (calculateTerm (sign,(head terms)) ass (Table attrs
              (Compositiontable cmpentries) convtbl refltbl models) symbs)
              (calculateTerm (sign,(head (tail terms))) ass (Table attrs
              (Compositiontable cmpentries) convtbl refltbl models) symbs)
applyOperation "RA_union" (sign,terms) table ass symbs = union
              (calculateTerm (sign,(head terms)) ass table symbs)
              (calculateTerm (sign,(head(tail terms))) ass table symbs)
applyOperation "RA_complement" (sign,terms) (Table (Table_Attrs name id_
               baserels) comptbl convtbl refltbl models) ass symbs =
               complement
               (calculateTerm (sign,(head terms)) ass (Table (Table_Attrs
               name id_ baserels) comptbl convtbl refltbl models)
               symbs) baserels
applyOperation "RA_identity" _ (Table (Table_Attrs _ id_ _)
               _ _ _ _) _ _ = [id_]
applyOperation "RA_converse" (sign,terms)
    (Table attrs cmptable cnvtable refltbl models) ass symbs =
  calculateConverse cnvtable
    (calculateTerm (sign,(head terms)) ass
     (Table attrs cmptable cnvtable refltbl models) symbs)

applyOperation "RA_shortcut" (sign,terms) (Table attrs comptbl
                (Conversetable_Ternary inv shortc hom) refltbl
                models) ass symbs = calculateConverseTernary shortc
                (calculateTerm (sign,(head terms)) ass (Table attrs comptbl
                (Conversetable_Ternary inv shortc hom) refltbl
                models) symbs)
applyOperation "RA_inverse" (sign,terms) (Table attrs comptbl
                (Conversetable_Ternary inv shortc hom) refltbl
                models) ass symbs = calculateConverseTernary inv
                (calculateTerm (sign,(head terms)) ass (Table attrs comptbl
                (Conversetable_Ternary inv shortc hom) refltbl
                models) symbs)

applyOperation "RA_homing" (sign,terms) (Table attrs comptbl
                (Conversetable_Ternary inv shortc hom) refltbl
                models) ass symbs = calculateConverseTernary hom
                (calculateTerm (sign,(head terms)) ass (Table attrs comptbl
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

calculateConverse:: Conversetable -> [Baserel] -> [Baserel]
calculateConverse (Conversetable_Ternary _ _ _) _ = []
calculateConverse (Conversetable centries) rels =
    concatMap (calculateConverseAtomar rels) centries

calculateConverseAtomar :: [Baserel] -> Contabentry -> [Baserel]
calculateConverseAtomar rels (Contabentry rel1 rel2) =
   if elem rel1 rels then [rel2] else []

calculateConverseTernary :: [Contabentry_Ternary] -> [Baserel]
                         -> [Baserel]
calculateConverseTernary entries rels =
    concatMap (calculateConverseTernaryAtomar rels) entries

calculateConverseTernaryAtomar :: [Baserel] -> Contabentry_Ternary -> [Baserel]
calculateConverseTernaryAtomar rels2 (Contabentry_Ternary rel1 rels1) =
  if elem rel1 rels2 then rels1 else []

getBaseRelForVariable :: VAR -> VARIABLE_ASSIGNMENT ->[Baserel]
getBaseRelForVariable var (Variable_Assignment tuples) =
    concatMap (getBaseRelForVariableAtomar var) tuples

getBaseRelForVariableAtomar :: VAR -> (VAR, Baserel) -> [Baserel]
getBaseRelForVariableAtomar v (var, baserel) =
  if v == var then [baserel] else []

calculateFormula :: (Sign () (), FORMULA ()) -> VARIABLE_ASSIGNMENT -> Table
                 -> [(OP_SYMB, String)] -> Bool
calculateFormula (sign, qf) varass t symbs = case qf of
    Quantification _ vardecls _ _ ->
                 let (Result _ res) = (calculateQuantification (sign, qf)
                                       (appendVariableAssignments
                                       varass vardecls t) t symbs)
                 in res == Just True
    Conjunction formulas _ ->
        and [calculateFormula (sign,x) varass t symbs | x <- formulas]

    Disjunction formulas _ ->
        or [calculateFormula (sign,x) varass t symbs | x <- formulas]
    Implication f1 f2 _ _ ->
                 let test1 = calculateFormula (sign,f1) varass t symbs
                     test2 = calculateFormula (sign,f2) varass t symbs
                 in not (test1 && not test2)
    Equivalence f1 f2 _ ->
                 let test1 = calculateFormula (sign,f1) varass t symbs
                     test2 = calculateFormula (sign,f2) varass t symbs
                 in test1 == test2

    Negation f _ -> not (calculateFormula (sign,f) varass t symbs)
    True_atom _ -> True
    False_atom _ -> False
    Strong_equation term1 term2 _ ->
                 let t1 = calculateTerm (sign,term1) varass t symbs
                     t2 = calculateTerm (sign,term2) varass t symbs
                 in if equalElements t1 t2 then True
                    else False
    _ -> error $ "CASL.CompositionTable.ModelChecker.calculateFormula "
         ++ showDoc qf ""

equalElements :: [Baserel] -> [Baserel] -> Bool
equalElements a b = Set.fromList a == Set.fromList b

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
                                           baserels)   xs
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
appendAssignmentSingle1 acc var rel  = (var, rel) : acc

getVars:: [VAR_DECL] -> [VAR]
getVars = concatMap getVarsAtomic

getVarsAtomic:: VAR_DECL -> [VAR]
getVarsAtomic (Var_decl vars _ _) = vars

getBaseRelations:: Table -> [Baserel]
getBaseRelations (Table (Table_Attrs _ _ br) _ _ _ _) = br

appendVariableAssignments :: VARIABLE_ASSIGNMENT -> [VAR_DECL] -> Table
                          -> [VARIABLE_ASSIGNMENT]
appendVariableAssignments vars decls t =
     map (concatAssignment vars) (generateVariableAssignments decls t)
