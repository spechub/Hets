{-# LANGUAGE CPP #-}
{- |
Module      :  ./CASL/CompositionTable/ModelChecker.hs
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
import qualified Data.HashMap.Strict as Map

import Data.Function
import Data.Maybe
import Data.List

modelCheck :: Int -> (Sign () (), [Named (FORMULA ())])
           -> Table2 -> Result ()
modelCheck c (sign, sent) t = do
  let sm = Map.fromList $ extractAnnotations (annoMap sign)
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

modelCheckTest :: Int -> Map.HashMap OP_SYMB String -> Sign () () -> Table2
  -> Named (FORMULA ()) -> Result ()
modelCheckTest c symbs sign t x = let
    (n, d) = modelCheckTest1 c (sentence x) t symbs
    fstr = shows (printTheoryFormula (mapNamed (simplify_sen CASL sign) x)) "\n"
      in if null d
      then hint () ("Formula succeeded:\n" ++ fstr) nullRange
      else warning () ("Formula failed:\n" ++ fstr ++ show n
               ++ " counter example" ++ (if n > 1 then "s" else "")
               ++ ":\n" ++ intercalate "\n" d) nullRange

ifind :: Int -> IntMap.IntMap a -> a
ifind = IntMap.findWithDefault (error "CompositionTable.ifind")

modelCheckTest1 :: Int -> FORMULA () -> Table2 -> Map.HashMap OP_SYMB String
  -> (Int, [String])
modelCheckTest1 c sen t symbs = let
  vs = number $ Set.toList $ vars sen
  vm = Map.fromList vs
  rm = IntMap.fromList $ map (\ (a, b) -> (b, show a)) vs
  nf = foldFormula (fromCASL symbs vm) sen
  in case nf of
    Quant quant decl f -> calculateQuantification (Just c) (`ifind` rm)
        quant f t $ generateVariableAssignments decl t
    _ -> if calculateFormula t IntMap.empty nf then
       (0, []) else (1, ["formula as given above."])

calculateQuantification :: Maybe Int -> (Int -> String) -> QUANTIFIER -> Form
  -> Table2 -> [Assignment] -> (Int, [String])
calculateQuantification mc si quant f t@(Table2 _ _ l _ _ _) vs =
      let calc ass = calculateFormula t ass f
          nD = showAssignments si l
      in case quant of
           Universal -> case mc of
             Just c -> let
               fall (c0, ds) ass = let
                 res = calc ass
                 nC0 = if res then c0 else c0 + 1
                 nDs = if res || nC0 > c then ds else nD ass : ds
                 in seq (seq nC0 nDs) (nC0, nDs)
               in foldl' fall (0, []) vs
             Nothing -> foldr (\ ass p@(_, ds) ->
               if null ds then if calc ass then p else (1, [nD ass]) else p)
               (0, []) vs
           Existential -> if any calc vs then (0, []) else
               (1, ["Existential not fulfilled"])
           Unique_existential -> let
               funi ass ds = case ds of
                 _ : _ : _ -> ds
                 _ | calc ass -> nD ass : ds
                 _ -> ds
             in case foldr funi [] vs of
             [] -> (1, ["Unique Existential not fulfilled"])
             [_] -> (0, [])
             ds -> (1, ds)

type Assignment = IntMap.IntMap Int

showAssignments :: (Int -> String) -> IntMap.IntMap Baserel -> Assignment
  -> String
showAssignments si l xs =
    '[' : intercalate ", " (map (showSingleAssignment si l) $ IntMap.toList xs)
     ++ "]"

showSingleAssignment :: (Int -> String) -> IntMap.IntMap Baserel -> (Int, Int)
  -> String
showSingleAssignment si m (v, i) = si v ++ "->" ++ case ifind i m of
  Baserel b -> b

calculateTerm :: Assignment -> Table2 -> Term -> BSet
calculateTerm ass t trm = case trm of
    Var var -> getBaseRelForVariable var ass
    Appl opSymb terms -> applyOperation opSymb terms t ass
    Cond t1 fo t2 -> on (\ a b -> if calculateFormula t ass fo then a else b)
      (calculateTerm ass t) t1 t2

applyOperation :: Op -> [Term] -> Table2 -> Assignment -> BSet
applyOperation ra ts table@(Table2 _ id_ _ baserels cmpentries convtbl) ass =
  let err = error "CompositionTable.applyOperator"
  in case ts of
    ft : rt -> let r1 = calculateTerm ass table ft
      in case rt of
         [sd] -> case ra of
               Comp -> calculateComposition cmpentries r1
               Inter -> IntSet.intersection r1
               Union -> IntSet.union r1
               _ -> err
             $ calculateTerm ass table sd
         [] -> let (conv, inv, shortc, hom) = convtbl in case ra of
             Compl -> IntSet.difference baserels
             Conv -> calculateConverse conv
             Shortcut -> calculateConverse shortc
             Inv -> calculateConverse inv
             Home -> calculateConverse hom
             _ -> err
           $ r1
         _ -> err
    [] -> case ra of
      One -> baserels
      Iden -> IntSet.singleton id_
      Zero -> IntSet.empty
      _ -> err

intSetFold :: (Int -> b -> b) -> b -> IntSet.IntSet -> b
intSetFold =
#if __GLASGOW_HASKELL__ < 704
  IntSet.fold
#else
  IntSet.foldr'
#endif

calculateComposition :: CmpTbl -> BSet -> BSet -> BSet
calculateComposition entries rels1 rels2 = intSetFold
  (\ s1 t -> case ifind s1 entries of
      m1 -> intSetFold
         (\ s2 -> case ifind s2 m1 of
            m2 -> IntSet.union m2)
         t rels2)
  IntSet.empty rels1

calculateConverse :: ConTable -> BSet -> BSet
calculateConverse t =
    IntSet.unions . map (`ifind` t)
    . IntSet.toList

getBaseRelForVariable :: Int -> Assignment -> BSet
getBaseRelForVariable var = IntSet.singleton . ifind var

calculateFormula :: Table2 -> Assignment -> Form -> Bool
calculateFormula t varass qf = case qf of
    Quant q vardecls f ->
       null . snd . calculateQuantification Nothing show q f t
         $ appendVariableAssignments varass vardecls t
    Junct j formulas -> (if j then all else any)
        (calculateFormula t varass) formulas
    Impl isImpl f1 f2 -> on (if isImpl then (<=) else (==))
                 (calculateFormula t varass) f1 f2
    Neg f -> not $ calculateFormula t varass f
    Const b -> b
    Eq term1 term2 -> on (==) (calculateTerm varass t) term1 term2

generateVariableAssignments :: [Int] -> Table2 -> [Assignment]
generateVariableAssignments vs =
  gVAs vs . IntSet.toList . getBaseRelations

gVAs :: [Int] -> [Int] -> [Assignment]
gVAs vs brs = foldr (\ v rs -> [IntMap.insert v b r | b <- brs, r <- rs])
  [IntMap.empty] vs

getBaseRelations :: Table2 -> BSet
getBaseRelations (Table2 _ _ _ br _ _) = br

appendVariableAssignments :: Assignment -> [Int] -> Table2 -> [Assignment]
appendVariableAssignments vm decls t =
     map (`IntMap.union` vm) (generateVariableAssignments decls t)
