{-# LANGUAGE CPP #-}
{- |
Module      :  $Header$
Description :  checks validity of models regarding a composition table
Copyright   :  (c) Uni Bremen 2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable

checks validity of models regarding a composition table
-}

module CASL.CompositionTable.ModelChecker (modelCheck) where

import CASL.CompositionTable.CompositionTable
import CASL.CompositionTable.ModelTable
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

modelCheckTest :: Int -> [(OP_SYMB, String)] -> Sign () () -> Table2
  -> Named (FORMULA ()) -> Result ()
modelCheckTest c symbs sign t x = let
    (n, d) = modelCheckTest1 c (sign, x) t symbs
    fstr = shows (printTheoryFormula (mapNamed (simplify_sen CASL sign) x)) "\n"
      in if null d
      then hint () ("Formula succeeded:\n" ++ fstr) nullRange
      else warning () ("Formula failed:\n" ++ fstr ++ show n
               ++ " counter example" ++ (if n > 1 then "s" else "")
               ++ ":\n" ++ intercalate "\n" d) nullRange

modelCheckTest1 :: Int -> (Sign () (), Named (FORMULA ())) -> Table2
                -> [(OP_SYMB, String)] -> (Int, [String])
modelCheckTest1 c (sign, nSen) t symbs = case sentence nSen of
    Quantification quant decl f _ -> calculateQuantification c sign quant f
                  t symbs $ generateVariableAssignments decl t
    f -> if calculateFormula (sign, f) t symbs Map.empty then
       (0, []) else (1, ["formula as given above."])

calculateQuantification :: Int -> Sign () () -> QUANTIFIER -> FORMULA ()
   -> Table2 -> [(OP_SYMB, String)] -> [Assignment] -> (Int, [String])
calculateQuantification c sign quant f t@(Table2 _ l _ _ _) symbs vardecls =
      case foldl' (\ (b0, b1, c0, ds) ass -> case
        calculateFormula (sign, f) t symbs ass of
          res -> let
              nB0 = if res then False else b0
              nB1 = if res then if b1 then False else b0 else b1
              nD = showAssignments l ass
              (nC0, nDs) = case quant of
                Universal -> (if res then c0 else c0 + 1,
                  if res || c0 >= c then ds else nD : ds)
                Unique_existential -> (c0,
                  if res && (b0 || b1) then nD : ds else ds)
                Existential -> (c0, ds)
            in seq (seq nB0 $ seq nB1 $ seq nC0 nDs)
              (nB0, nB1, nC0, nDs))
              (True, False, 0, []) vardecls of
        (b0, b1, cE, ds) -> case quant of
           Universal -> (cE, ds)
           Unique_existential -> if b1 then (0, []) else (1, ds)
           Existential ->
             if b0 then (1, ["Existential not fulfilled"]) else (0, [])

type Assignment = Map.Map VAR Int

showAssignments :: IntMap.IntMap Baserel -> Map.Map VAR Int -> String
showAssignments l xs =
    '[' : intercalate ", " (map (showSingleAssignment l) $ Map.toList xs) ++ "]"

showSingleAssignment :: IntMap.IntMap Baserel -> (VAR, Int) -> String
showSingleAssignment m (v, i) = show v ++ "->" ++ case IntMap.lookup i m of
  Just (Baserel b) -> b
  Nothing -> "*** ERROR ****"

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
              let res = calculateFormula (sign, fo) t symbs ass
              in if res then calculateTerm (sign, t1) ass t symbs
                 else calculateTerm (sign, t2) ass t symbs
    _ -> IntSet.empty

getIdentifierForSymb :: OP_SYMB -> [(OP_SYMB, String)] -> String
getIdentifierForSymb symb = concatMap (getIdentifierForSymbAtomar symb)

getIdentifierForSymbAtomar :: OP_SYMB -> (OP_SYMB, String) -> String
getIdentifierForSymbAtomar symb (symb2, s) = if symb == symb2 then s else ""

applyOperation :: String -> (Sign () (), [TERM ()]) -> Table2
               -> Assignment -> [(OP_SYMB, String)] -> BSet
applyOperation ra (sign, ts) table@(Table2 id_ _ baserels cmpentries convtbl)
  ass symbs = case ts of
    ft : rt -> let r1 = calculateTerm (sign, ft) ass table symbs
      in case rt of
         sd : _
           -> let r2 = calculateTerm (sign, sd) ass table symbs
            in case ra of
               "RA_composition" -> calculateComposition cmpentries r1 r2
               "RA_intersection" -> IntSet.intersection r1 r2
               "RA_union" -> IntSet.union r1 r2
               _ -> IntSet.empty
         _ -> let (conv, inv, shortc, hom) = convtbl in case ra of
           "RA_complement" -> IntSet.difference baserels r1
           "RA_converse" -> calculateConverse conv r1
           "RA_shortcut" -> calculateConverse shortc r1
           "RA_inverse" -> calculateConverse inv r1
           "RA_homing" -> calculateConverse hom r1
           _ -> IntSet.empty
    _ -> case ra of
      "RA_one" -> baserels
      "RA_identity" -> IntSet.singleton id_
      _ -> IntSet.empty

intSetFold :: (Int -> b -> b) -> b -> IntSet.IntSet -> b
intSetFold =
#if __GLASGOW_HASKELL__ < 704
  IntSet.fold
#else
  IntSet.foldr'
#endif

calculateComposition :: CmpTbl -> BSet -> BSet -> BSet
calculateComposition entries rels1 rels2 = intSetFold
  (\ s1 t -> case IntMap.findWithDefault IntMap.empty s1 entries of
      m1 -> intSetFold
         (\ s2 -> case IntMap.findWithDefault IntSet.empty s2 m1 of
            m2 -> IntSet.union m2)
         t rels2)
  IntSet.empty rels1

calculateConverse :: ConTable -> BSet -> BSet
calculateConverse t =
    IntSet.unions . map (\ i -> IntMap.findWithDefault IntSet.empty i t)
    . IntSet.toList

getBaseRelForVariable :: VAR -> Assignment -> BSet
getBaseRelForVariable var = maybe IntSet.empty IntSet.singleton . Map.lookup var

calculateFormula :: (Sign () (), FORMULA ()) -> Table2
                 -> [(OP_SYMB, String)] -> Assignment -> Bool
calculateFormula (sign, qf) t symbs varass = case qf of
    Quantification q vardecls f _ ->
       calculateQuantification 1 sign q f t symbs
         (appendVariableAssignments varass vardecls t) == (0, [])
    Junction j formulas _ -> (if j == Con then and else or)
        [calculateFormula (sign, x) t symbs varass | x <- formulas]
    Relation f1 rel f2 _ ->
                 let test1 = calculateFormula (sign, f1) t symbs varass
                     test2 = calculateFormula (sign, f2) t symbs varass
                 in rel == Equivalence && test1 == test2
                    || not (test1 && not test2)
    Negation f _ -> not (calculateFormula (sign, f) t symbs varass)
    Atom b _ -> b
    Equation term1 Strong term2 _ ->
      calculateTerm (sign, term1) varass t symbs
      == calculateTerm (sign, term2) varass t symbs
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
