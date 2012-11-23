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
           -> Table -> Result ()
modelCheck c (sign, sent) t =
  mapM_ (modelCheckTest c (extractAnnotations (annoMap sign)) sign t) sent

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

modelCheckTest :: Int -> [(OP_SYMB, String)] -> Sign () () -> Table
  -> Named (FORMULA ()) -> Result ()
modelCheckTest c symbs sign t x = let
    Result d _ = modelCheckTest1 (sign, x) t symbs
    n = length d
    fstr = shows (printTheoryFormula (mapNamed (simplify_sen CASL sign) x)) "\n"
      in if null d
      then hint () ("Formula succeeded:\n" ++ fstr) nullRange
      else warning () ("Formula failed:\n" ++ fstr ++ show n
               ++ " counter example" ++ (if n > 1 then "s" else "")
               ++ ":\n" ++ showDiagStrings (take c d)) nullRange

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
                  in if res1 == res2 then return True
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

type BSet = Set.Set Baserel

calculateTerm :: (Sign () (), TERM ()) -> VARIABLE_ASSIGNMENT -> Table
              -> [(OP_SYMB, String)] -> BSet
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
    _ -> Set.empty

getIdentifierForSymb :: OP_SYMB -> [(OP_SYMB, String)] -> String
getIdentifierForSymb symb = concatMap (getIdentifierForSymbAtomar symb)

getIdentifierForSymbAtomar :: OP_SYMB -> (OP_SYMB, String) -> String
getIdentifierForSymbAtomar symb (symb2, s) = if symb == symb2 then s else ""

applyOperation :: String -> (Sign () (), [TERM ()]) -> Table
               -> VARIABLE_ASSIGNMENT -> [(OP_SYMB, String)] -> BSet
applyOperation "RA_zero" (_, []) _ _ _ = Set.empty
applyOperation "RA_one" _ (Table (Table_Attrs _ _ baserels)
              _ _ _ _) _ _ = Set.fromList baserels
applyOperation "RA_intersection" (sign, ft : sd : _) table ass symbs =
              Set.intersection
              (calculateTerm (sign, ft) ass table symbs)
              (calculateTerm (sign, sd) ass table symbs)
applyOperation "RA_composition" (sign, ft : sd : _) (Table attrs
              (Compositiontable cmpentries) convtbl refltbl models)
              ass symbs = calculateComposition cmpentries
              (calculateTerm (sign, ft) ass (Table attrs
              (Compositiontable cmpentries) convtbl refltbl models) symbs)
              (calculateTerm (sign, sd) ass (Table attrs
              (Compositiontable cmpentries) convtbl refltbl models) symbs)
applyOperation "RA_union" (sign, ft : sd : _) table ass symbs = Set.union
              (calculateTerm (sign, ft) ass table symbs)
              (calculateTerm (sign, sd) ass table symbs)
applyOperation "RA_complement" (sign, ft : _) (Table (Table_Attrs name id_
               baserels) comptbl convtbl refltbl models) ass symbs =
               Set.difference (Set.fromList baserels)
               (calculateTerm (sign, ft) ass (Table (Table_Attrs
               name id_ baserels) comptbl convtbl refltbl models)
               symbs)
applyOperation "RA_identity" _ (Table (Table_Attrs _ id_ _)
               _ _ _ _) _ _ = Set.singleton id_
applyOperation "RA_converse" (sign, ft : _)
    tabl@(Table _ _ cnvtable _ _) ass symbs =
  calculateConverse cnvtable
    $ calculateTerm (sign, ft) ass tabl symbs

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
applyOperation _ _ _ _ _ = Set.empty

calculateComposition :: [Cmptabentry] -> BSet -> BSet -> BSet
calculateComposition entries rels1 rels2 =
    Set.unions $ map (calculateCompositionAux rels1 rels2) entries

calculateCompositionAux :: BSet -> BSet -> Cmptabentry -> BSet
calculateCompositionAux rels1 rels2
    (Cmptabentry (Cmptabentry_Attrs rel1 rel2) baserels) =
  if Set.member rel1 rels1 && Set.member rel2 rels2
  then Set.fromList baserels
  else Set.empty

calculateConverse :: Conversetable -> BSet -> BSet
calculateConverse (Conversetable_Ternary {}) _ = Set.empty
calculateConverse (Conversetable centries) rels =
    Set.unions $ map (calculateConverseAtomar rels) centries

calculateConverseAtomar :: BSet -> Contabentry -> BSet
calculateConverseAtomar rels (Contabentry rel1 rel2) =
   Set.unions [Set.fromList rel2 | Set.member rel1 rels]

calculateConverseTernary :: [Contabentry_Ternary] -> BSet -> BSet
calculateConverseTernary entries rels =
    Set.unions $ map (calculateConverseTernaryAtomar rels) entries

calculateConverseTernaryAtomar :: BSet -> Contabentry_Ternary -> BSet
calculateConverseTernaryAtomar rels2 (Contabentry_Ternary rel1 rels1) =
  if Set.member rel1 rels2 then Set.fromList rels1 else Set.empty

getBaseRelForVariable :: VAR -> VARIABLE_ASSIGNMENT -> BSet
getBaseRelForVariable var (Variable_Assignment tuples) =
    Set.unions $ map (getBaseRelForVariableAtomar var) tuples

getBaseRelForVariableAtomar :: VAR -> (VAR, Baserel) -> BSet
getBaseRelForVariableAtomar v (var, baserel) =
    Set.fromList [baserel | v == var]

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
                 in t1 == t2
    _ -> error $ "CASL.CompositionTable.ModelChecker.calculateFormula "
         ++ showDoc qf ""

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
