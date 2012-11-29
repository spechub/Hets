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
import CASL.CompositionTable.ModelFormula
import CASL.AS_Basic_CASL
import CASL.Fold
import CASL.Sign
import CASL.ToDoc
import CASL.Logic_CASL
import Logic.Logic

import Common.AS_Annotation
import Common.Result
import Common.Id
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
      sm = Map.fromList $ extractAnnotations (annoMap sign)
  mapM_ (modelCheckTest c sm sign t) sent

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

modelCheckTest :: Int -> Map.Map OP_SYMB String -> Sign () () -> Table2
  -> Named (FORMULA ()) -> Result ()
modelCheckTest c symbs sign t x = let
    (n, d) = modelCheckTest1 c (sentence x) t symbs
    fstr = shows (printTheoryFormula (mapNamed (simplify_sen CASL sign) x)) "\n"
      in if null d
      then hint () ("Formula succeeded:\n" ++ fstr) nullRange
      else warning () ("Formula failed:\n" ++ fstr ++ show n
               ++ " counter example" ++ (if n > 1 then "s" else "")
               ++ ":\n" ++ intercalate "\n" d) nullRange

modelCheckTest1 :: Int -> FORMULA () -> Table2 -> Map.Map OP_SYMB String
  -> (Int, [String])
modelCheckTest1 c sen t symbs = let
  vs = number $ Set.toList $ vars sen
  vm = Map.fromList vs
  rm = IntMap.fromList $ map (\ (a, b) -> (b, show a)) vs
  nf = foldFormula (fromCASL symbs vm) sen
  in case nf of
    Quant quant decl f -> calculateQuantification c
        (\ i -> IntMap.findWithDefault "Unknown" i rm)
        quant f t $ generateVariableAssignments decl t
    _ -> if calculateFormula nf t IntMap.empty then
       (0, []) else (1, ["formula as given above."])

calculateQuantification :: Int -> (Int -> String) -> QUANTIFIER -> Form
  -> Table2 -> [Assignment] -> (Int, [String])
calculateQuantification c si quant f t@(Table2 _ l _ _ _) vardecls =
      case foldl' (\ (b0, b1, c0, ds) ass -> case
        calculateFormula f t ass of
          res -> let
              nB0 = if res then False else b0
              nB1 = if res then if b1 then False else b0 else b1
              nD = showAssignments si l ass
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

type Assignment = IntMap.IntMap Int

showAssignments :: (Int -> String) -> IntMap.IntMap Baserel -> Assignment
  -> String
showAssignments si l xs =
    '[' : intercalate ", " (map (showSingleAssignment si l) $ IntMap.toList xs)
     ++ "]"

showSingleAssignment :: (Int -> String) -> IntMap.IntMap Baserel -> (Int, Int)
  -> String
showSingleAssignment si m (v, i) = si v ++ "->" ++ case IntMap.lookup i m of
  Just (Baserel b) -> b
  Nothing -> "*** ERROR ****"

calculateTerm :: Term -> Assignment -> Table2 -> BSet
calculateTerm trm ass t = case trm of
    Var var -> getBaseRelForVariable var ass
    Appl opSymb terms -> applyOperation opSymb terms t ass
    Cond t1 fo t2 ->
              let res = calculateFormula fo t ass
              in if res then calculateTerm t1 ass t
                 else calculateTerm t2 ass t

applyOperation :: Op -> [Term] -> Table2 -> Assignment -> BSet
applyOperation ra ts table@(Table2 id_ _ baserels cmpentries convtbl) ass =
  case ts of
    ft : rt -> let r1 = calculateTerm ft ass table
      in case rt of
         sd : _
           -> let r2 = calculateTerm sd ass table
            in case ra of
               Comp -> calculateComposition cmpentries r1 r2
               Inter -> IntSet.intersection r1 r2
               Union -> IntSet.union r1 r2
               _ -> IntSet.empty
         _ -> let (conv, inv, shortc, hom) = convtbl in case ra of
           Compl -> IntSet.difference baserels r1
           Conv -> calculateConverse conv r1
           Shortcut -> calculateConverse shortc r1
           Inv -> calculateConverse inv r1
           Home -> calculateConverse hom r1
           _ -> IntSet.empty
    _ -> case ra of
      One -> baserels
      Iden -> IntSet.singleton id_
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

getBaseRelForVariable :: Int -> Assignment -> BSet
getBaseRelForVariable var =
  maybe IntSet.empty IntSet.singleton . IntMap.lookup var

calculateFormula :: Form -> Table2 -> Assignment -> Bool
calculateFormula qf t varass = case qf of
    Quant q vardecls f ->
       calculateQuantification 1 show q f t
         (appendVariableAssignments varass vardecls t) == (0, [])
    Junct j formulas -> (if j then and else or)
        [calculateFormula x t varass | x <- formulas]
    Impl isImpl f1 f2 ->
                 let test1 = calculateFormula f1 t varass
                     test2 = calculateFormula f2 t varass
                 in not isImpl && test1 == test2
                    || not (test1 && not test2)
    Neg f -> not $ calculateFormula f t varass
    Const b -> b
    Eq term1 term2 ->
      calculateTerm term1 varass t
      == calculateTerm term2 varass t

generateVariableAssignments :: [Int] -> Table2 -> [Assignment]
generateVariableAssignments vs =
  gVAs vs . IntSet.toList . getBaseRelations

gVAs :: [Int] -> [Int] -> [Assignment]
gVAs vs brs = foldr (\ v rs -> [IntMap.insert v b r | b <- brs, r <- rs])
  [IntMap.empty] vs

getBaseRelations :: Table2 -> BSet
getBaseRelations (Table2 _ _ br _ _) = br

appendVariableAssignments :: Assignment -> [Int] -> Table2 -> [Assignment]
appendVariableAssignments vm decls t =
     map (`IntMap.union` vm) (generateVariableAssignments decls t)
