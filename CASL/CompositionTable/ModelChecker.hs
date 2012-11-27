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

module CASL.CompositionTable.ModelChecker (modelCheck) where

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
import Common.Utils

import qualified Data.Set as Set
import qualified Data.IntSet as IntSet
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import Data.Maybe
import Data.List

modelCheck :: Int -> (Sign () (), [Named (FORMULA ())])
           -> Table -> Result ()
modelCheck c (sign, sent) t1 = do
  let t = toTable2 t1
  mapM_ (modelCheckTest c (extractAnnotations (annoMap sign)) sign t) sent

data Table2 = Table2 Int (IntMap.IntMap Baserel) BSet CmpTbl ConTables

type CmpTbl = IntMap.IntMap (IntMap.IntMap IntSet.IntSet)

type ConTable = IntMap.IntMap IntSet.IntSet

type ConTables = (ConTable, ConTable, ConTable, ConTable)

lkup :: Ord a => a -> Map.Map a Int -> Int
lkup = Map.findWithDefault 0

toTable2 :: Table -> Table2
toTable2 (Table (Table_Attrs _ id_ baserels)
  (Compositiontable comptbl) convtbl _ _) =
  let ns = number baserels
      m = Map.fromList $ number baserels
  in Table2 (lkup id_ m)
    (IntMap.fromList $ map (\ (a, b) -> (b, a)) ns)
    (IntSet.fromAscList [1 .. Map.size m])
    (toCmpTbl m comptbl)
    $ toConTables m convtbl

toCmpTbl :: Map.Map Baserel Int -> [Cmptabentry] -> CmpTbl
toCmpTbl m =
  foldl' (\ t (Cmptabentry (Cmptabentry_Attrs rel1 rel2) bs)
              -> IntMap.insertWith IntMap.union (lkup rel1 m)
                 (IntMap.insertWith IntSet.union (lkup rel2 m)
                 (IntSet.fromList $ map (`lkup` m) bs) IntMap.empty) t)
  IntMap.empty

toConTab :: Map.Map Baserel Int -> (a -> Baserel) -> (a -> [Baserel]) -> [a]
  -> ConTable
toConTab m s1 s2 = foldl' (\ t a ->
    IntMap.insertWith IntSet.union (lkup (s1 a) m)
           (IntSet.fromList $ map (`lkup` m) $ s2 a) t) IntMap.empty

toConTab2 :: Map.Map Baserel Int -> [Contabentry_Ternary] -> ConTable
toConTab2 m =
  toConTab m contabentry_TernaryArgBaseRel contabentry_TernaryConverseBaseRels

toConTables :: Map.Map Baserel Int -> Conversetable -> ConTables
toConTables m c = case c of
  Conversetable l ->
    (toConTab m contabentryArgBaseRel contabentryConverseBaseRel l
    , IntMap.empty, IntMap.empty, IntMap.empty)
  Conversetable_Ternary l1 l2 l3 ->
    (IntMap.empty, toConTab2 m l1, toConTab2 m l2, toConTab2 m l3)

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

modelCheckTest :: Int -> [(OP_SYMB, String)] -> Sign () () -> Table2
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

modelCheckTest1 :: (Sign () (), Named (FORMULA ())) -> Table2
                -> [(OP_SYMB, String)] -> Result Bool
modelCheckTest1 (sign, nSen) t symbs =
  let varass = Map.empty in case sentence nSen of
    Junction j formulas range -> let
        bs = map (\ f -> calculateFormula (sign, f) varass t symbs)
             formulas
        res = if j == Con then and else or
        in if res bs then return True else
            warning False (show j ++ "junction does not hold:"
                                 ++ showDoc (map (simplify_sen CASL sign)
                                 formulas) "") range
    f@(Relation f1 c f2 range) ->
                  let test1 = calculateFormula (sign, f1) varass t symbs
                      test2 = calculateFormula (sign, f2) varass t symbs
                      res = not (test1 && not test2)
                  in if if c == Equivalence then test1 == test2 else res
                     then return True
                     else warning False ("Relation does not hold: " ++
                          showDoc (simplify_sen CASL sign f) "") range
    Negation f range ->
                  let res = calculateFormula (sign, f) varass t symbs
                  in if not res then return True
                    else warning False
                                        ("Negation does not hold:"
                                        ++ showDoc (simplify_sen CASL
                                                   sign f) "") range
    Atom b range -> if b then return True else
      warning False "False-atom can't be fulfilled!" range
    Equation t1 Strong t2 range ->
                  let res1 = calculateTerm (sign, t1) varass t symbs
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

calculateQuantification :: (Sign () (), FORMULA ()) -> [Assignment]
                        -> Table2 -> [(OP_SYMB, String)] -> Result Bool
calculateQuantification (sign, qf) vardecls t@(Table2 _ l _ _ _) symbs =
  case qf of
    Quantification quant _ f range ->
        let tuples = map ( \ ass -> let
                res = calculateFormula (sign, f) ass t symbs
                in if res then (res, "")
                   else (res, ' ' : showAssignments l ass))
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

type Assignment = Map.Map VAR Int

showAssignments :: IntMap.IntMap Baserel -> Map.Map VAR Int -> String
showAssignments l xs =
    '[' : intercalate ", " (map (showSingleAssignment l) $ Map.toList xs) ++ "]"

showSingleAssignment :: IntMap.IntMap Baserel -> (VAR, Int) -> String
showSingleAssignment m (v, i) = show v ++ "->" ++ case IntMap.lookup i m of
  Just (Baserel b) -> b
  Nothing -> "*** ERROR ****"

type BSet = IntSet.IntSet

calculateTerm :: (Sign () (), TERM ()) -> Assignment -> Table2
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
    _ -> IntSet.empty

getIdentifierForSymb :: OP_SYMB -> [(OP_SYMB, String)] -> String
getIdentifierForSymb symb = concatMap (getIdentifierForSymbAtomar symb)

getIdentifierForSymbAtomar :: OP_SYMB -> (OP_SYMB, String) -> String
getIdentifierForSymbAtomar symb (symb2, s) = if symb == symb2 then s else ""

applyOperation :: String -> (Sign () (), [TERM ()]) -> Table2
               -> Assignment -> [(OP_SYMB, String)] -> BSet
applyOperation ra (sign, ts) table@(Table2 _ _ baserels cmpentries convtbl)
  ass symbs = case ts of
    ft : rt -> let r1 = calculateTerm (sign, ft) ass table symbs
      in case rt of
         sd : _ | elem ra ["RA_composition", "RA_intersection", "RA_union"]
           -> let r2 = calculateTerm (sign, sd) ass table symbs
            in case ra of
               "RA_composition" -> calculateComposition cmpentries r1 r2
               "RA_intersection" -> IntSet.intersection r1 r2
               _ -> IntSet.union r1 r2
         _ -> let (conv, inv, shortc, hom) = convtbl in case ra of
           "RA_complement" -> IntSet.difference baserels r1
           "RA_converse" -> calculateConverse conv r1
           "RA_shortcut" -> calculateConverse shortc r1
           "RA_inverse" -> calculateConverse inv r1
           "RA_homing" -> calculateConverse hom r1
           _ -> defOp ra table
    _ -> defOp ra table

defOp :: String -> Table2 -> BSet
defOp ra (Table2 id_ _ baserels _ _) = case ra of
  "RA_one" -> baserels
  "RA_identity" -> IntSet.singleton id_
  _ -> IntSet.empty

calculateComposition :: CmpTbl -> BSet -> BSet -> BSet
calculateComposition entries rels1 rels2 =
  IntSet.fold (\ s1 t ->
    let m1 = IntMap.findWithDefault IntMap.empty s1 entries in
    IntSet.fold (\ s2 -> IntSet.union
                 $ IntMap.findWithDefault IntSet.empty s2 m1) t rels2)
  IntSet.empty rels1

calculateConverse :: ConTable -> BSet -> BSet
calculateConverse t =
    IntSet.unions . map (\ i -> IntMap.findWithDefault IntSet.empty i t)
    . IntSet.toList

getBaseRelForVariable :: VAR -> Assignment -> BSet
getBaseRelForVariable var = maybe IntSet.empty IntSet.singleton . Map.lookup var

calculateFormula :: (Sign () (), FORMULA ()) -> Assignment -> Table2
                 -> [(OP_SYMB, String)] -> Bool
calculateFormula (sign, qf) varass t symbs = case qf of
    Quantification _ vardecls _ _ ->
                 let Result _ res = calculateQuantification (sign, qf)
                                       (appendVariableAssignments
                                       varass vardecls t) t symbs
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

generateVariableAssignments :: [VAR_DECL] -> Table2 -> [Assignment]
generateVariableAssignments vardecls =
  let vs = Set.fromList $ getVars vardecls in
  gVAs vs . IntSet.toList . getBaseRelations

gVAs :: Set.Set VAR -> [Int] -> [Assignment]
gVAs vs brs = Set.fold (\ v rs -> [Map.insert v b r | b <- brs, r <- rs])
  [Map.empty] vs

getVars :: [VAR_DECL] -> [VAR]
getVars = concatMap getVarsAtomic

getVarsAtomic :: VAR_DECL -> [VAR]
getVarsAtomic (Var_decl vars _ _) = vars

getBaseRelations :: Table2 -> BSet
getBaseRelations (Table2 _ _ br _ _) = br

appendVariableAssignments :: Assignment -> [VAR_DECL] -> Table2 -> [Assignment]
appendVariableAssignments vars decls t =
     map (Map.union vars) (generateVariableAssignments decls t)
