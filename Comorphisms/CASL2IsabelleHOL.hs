{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski and Uni Bremen 2003
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

   The embedding comorphism from CASL to Isabelle-HOL.
-}

{- todo
    disambiguate names (i.e. those coming from Main)
-}

module Comorphisms.CASL2IsabelleHOL where

import Logic.Logic
import Logic.Comorphism
import Common.AS_Annotation
import qualified Common.Lib.Map as Map
import Common.Lib.Set as Set
import Data.List as List
import Data.Maybe
import Data.Char
import Common.AS_Annotation (Named, mapNamedM)
import Debug.Trace
-- CASL
import CASL.Logic_CASL 
import CASL.AS_Basic_CASL
import CASL.Sublogic
import CASL.Sign
import CASL.Morphism
import CASL.Quantification 

-- Isabelle
import Isabelle.IsaSign as IsaSign
import Isabelle.IsaConsts
import Isabelle.Logic_Isabelle
import Isabelle.Translate

-- | The identity of the comorphism
data CASL2IsabelleHOL = CASL2IsabelleHOL deriving (Show)

-- Isabelle theories
type IsaTheory = (IsaSign.Sign,[Named IsaSign.Sentence])

-- extended signature translation
type SignTranslator f e = CASL.Sign.Sign f e -> e -> IsaTheory -> IsaTheory

-- extended signature translation for CASL
sigTrCASL :: SignTranslator () ()
sigTrCASL _ _ = id

-- extended formula translation
type FormulaTranslator f e = CASL.Sign.Sign f e -> f -> Term

-- extended formula translation for CASL
formTrCASL :: FormulaTranslator () ()
formTrCASL _ _ = error "CASL2IsabelleHOL: No extended formulas allowed in CASL"

instance Language CASL2IsabelleHOL -- default definition is okay

instance Comorphism CASL2IsabelleHOL
               CASL CASL.Sublogic.CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign 
               CASLMor
               CASL.Morphism.Symbol CASL.Morphism.RawSymbol ()
               Isabelle () () IsaSign.Sentence () ()
               IsaSign.Sign 
               () () () ()  where
    sourceLogic _ = CASL
    sourceSublogic _ = CASL_SL
                      { has_sub = False, -- no subsorting yet ...
                        has_part = False, -- no partiality yet ...
                        has_cons = True,
                        has_eq = True,
                        has_pred = True,
                        which_logic = FOL
                      }
    targetLogic _ = Isabelle
    targetSublogic _ = ()
    map_theory _ = transTheory sigTrCASL formTrCASL
    --map_morphism _ morphism1 -> Maybe morphism2
    map_sentence _ sign =
      Just . mapSen formTrCASL sign
    --map_symbol :: cid -> symbol1 -> Set symbol2

------------------------------ Ids ---------------------------------


---------------------------- Signature -----------------------------

transTheory :: SignTranslator f e ->
               FormulaTranslator f e ->
               (CASL.Sign.Sign f e, [Named (FORMULA f)])
                   -> Maybe IsaTheory 
transTheory trSig trForm (sign,sens) = 
  fmap (trSig sign (extendedInfo sign)) $
  Just(IsaSign.emptySign {
    baseSig = "Main",
    tsig = emptyTypeSig 
            {arities = Set.fold (\s -> Map.insert (showIsa s) [(isaTerm, [])]) 
                               Map.empty (sortSet sign)},
    constTab = Map.foldWithKey insertOps
                  (Map.foldWithKey insertPreds
                                   Map.empty
                                   (predMap sign))
                  (opMap sign),
    dataTypeTab = makeDtDefs sign $ sens },
     map (mapNamed (mapSen trForm sign)) sens)  -- for now, no new sentences
  where 
    insertOps op ts m = 
     if Set.size ts == 1 
      then Map.insert (showIsa op) (transOpType (Set.findMin ts)) m
      else
      foldl (\m1 (t,i) -> Map.insert (showIsaI op i) (transOpType t) m1) m 
            (zip (Set.toList ts) [1..size ts])
    insertPreds pre ts m =
     if Set.size ts == 1 
      then Map.insert (showIsa pre) (transPredType (Set.findMin ts)) m
      else
      foldl (\m1 (t,i) -> Map.insert (showIsaI pre i) (transPredType t) m1) m 
            (zip (Set.toList ts) [1..size ts])
 
makeDtDefs :: CASL.Sign.Sign f e -> [Named (FORMULA f)] 
               -> [[(Typ,[(String,[Typ])])]]
makeDtDefs sign = mapMaybe $ makeDtDef sign

makeDtDef :: CASL.Sign.Sign f e -> Named (FORMULA f) -> 
             Maybe [(Typ,[(String,[Typ])])]
makeDtDef sign (NamedSen _ (Sort_gen_ax constrs True)) =
  Just(map makeDt srts)
  where 
  (srts,ops,_maps) = recover_Sort_gen_ax constrs
  makeDt s = (transSort s, map makeOp (List.filter (hasTheSort s) ops))
  makeOp opSym = (transOP_SYMB sign opSym, transArgs opSym)
  hasTheSort s (Qual_op_name _ ot _) = s == res_OP_TYPE ot 
  hasTheSort _ _ = error "CASL2IsabelleHOL.hasTheSort"
  transArgs (Qual_op_name _ ot _) = map transSort $ args_OP_TYPE ot
  transArgs _ = error "CASL2IsabelleHOL.transArgs"
makeDtDef _ _ = Nothing

transSort :: SORT -> Typ
transSort s = Type (showIsa s) [] [] []

transOpType :: OpType -> Typ
transOpType ot = mkCurryFunType (map transSort $ opArgs ot) 
                 $ transSort (opRes ot)

transPredType :: PredType -> Typ
transPredType pt = mkCurryFunType (map transSort $ predArgs pt) boolType


------------------------------ Formulas ------------------------------

var :: String -> Term
var v = IsaSign.Free v noType isaTerm

transVar :: VAR -> String
transVar = showIsaSid

xvar :: Int -> String
xvar i = if i<=26 then [chr (i+ord('a'))] else "x"++show i

rvar :: Int -> String
rvar i = if i<=9 then [chr (i+ord('R'))] else "R"++show i

quantifyIsa :: String -> (String, Typ) -> Term -> Term
quantifyIsa q (v,t) phi =
  App (Const q noType isaTerm) (Abs (Const v noType isaTerm) t phi NotCont)
      NotCont

quantify :: QUANTIFIER -> (VAR, SORT) -> Term -> Term
quantify q (v,t) phi  = 
  quantifyIsa (qname q) (transVar v, transSort t) phi
  where
  qname Universal = allS
  qname Existential = exS
  qname Unique_existential = ex1S

transOP_SYMB :: CASL.Sign.Sign f e -> OP_SYMB -> String
transOP_SYMB sign (Qual_op_name op ot _) = 
  case (do ots <- Map.lookup op (opMap sign)
           if Set.size ots == 1 then return $ showIsa op
            else do i <- elemIndex (toOpType ot) (Set.toList ots)
                    return $ showIsaI op (i+1)) of
    Just str -> str  
    Nothing -> showIsa op
transOP_SYMB _ (Op_name _) = error "CASL2Isabelle: unqualified operation"

transPRED_SYMB :: CASL.Sign.Sign f e -> PRED_SYMB -> String
transPRED_SYMB sign (Qual_pred_name p pt _) =
  case (do pts <- Map.lookup p (predMap sign)
           if Set.size pts == 1 then return $ showIsa p 
            else do i <- elemIndex (toPredType pt) (Set.toList pts)
                    return $ showIsaI p (i+1)) of
    Just str -> str
    Nothing -> error "CASL2Isabelle: showIsa p"
transPRED_SYMB _ (Pred_name _) = error "CASL2Isabelle: unqualified predicate"

mapSen :: FormulaTranslator f e -> CASL.Sign.Sign f e -> FORMULA f -> Sentence
mapSen trFrom sign phi = 
  Sentence {senTerm = transFORMULA sign trFrom (stripQuant phi)}


transFORMULA :: CASL.Sign.Sign f e -> FormulaTranslator f e 
                -> FORMULA f -> Term
transFORMULA sign tr (Quantification qu vdecl phi _) =
  foldr (quantify qu) (transFORMULA sign tr phi) (flatVAR_DECLs vdecl)
transFORMULA sign tr (Conjunction phis _) =
  if null phis then true
  else foldl1 binConj (map (transFORMULA sign tr) phis)
transFORMULA sign tr (Disjunction phis _) =
  if null phis then false
  else foldl1 binDisj (map (transFORMULA sign tr) phis)
transFORMULA sign tr (Implication phi1 phi2 _ _) =
  binImpl (transFORMULA sign tr phi1) (transFORMULA sign tr phi2)
transFORMULA sign tr (Equivalence phi1 phi2 _) =
  binEqv (transFORMULA sign tr phi1) (transFORMULA sign tr phi2)
transFORMULA sign tr (Negation phi _) =
  termAppl notOp (transFORMULA sign tr phi)
transFORMULA _sign _tr (True_atom _) =
  true
transFORMULA _sign _tr (False_atom _) =
  false
transFORMULA sign tr (Predication psymb args _) =
  foldl termAppl
            (con $ transPRED_SYMB sign psymb)
            (map (transTERM sign tr) args)
transFORMULA _sign _tr (Definedness _t _) =
  true
transFORMULA sign tr (Existl_equation t1 t2 _) =
  binEq (transTERM sign tr t1) (transTERM sign tr t2)
transFORMULA sign tr (Strong_equation t1 t2 _) =
  binEq (transTERM sign tr t1) (transTERM sign tr t2)
transFORMULA sign tr (Membership t1 s _) =
  trace "WARNING: ignoring membership formula" $ true
  --error "No translation for membership"
transFORMULA sign tr (Sort_gen_ax constrs _) =
   trace "WARNING: ignoring sort generation constraints" 
          $ true
  --error "No translation for sort generation constraints"
transFORMULA _sign _tr (Mixfix_formula _) = 
  error "No translation for mixfix formulas"
transFORMULA _sign _tr (Unparsed_formula _ _) = 
  error "No translation for unparsed formulas"
transFORMULA sign tr (ExtFORMULA phi) =
  tr sign phi

transTERM :: CASL.Sign.Sign f e
	     -> (CASL.Sign.Sign f e -> f -> Term) -> TERM f -> Term
transTERM _sign _tr (Qual_var v _s _) =
  var $ transVar v
transTERM sign tr (Application opsymb args _) =
  foldl termAppl
            (con $ transOP_SYMB sign opsymb)
            (map (transTERM sign tr) args)
transTERM sign tr (Sorted_term t _s _) =
  transTERM sign tr t
transTERM sign tr (Cast t _s _) =
  transTERM sign tr t -- ??? Should lead to an error!
transTERM sign tr (Conditional t1 phi t2 _) =
  foldl termAppl (con "If") [transFORMULA sign tr phi,
       transTERM sign tr t1, transTERM sign tr t2]
transTERM _sign _tr (Simple_id v) =
  IsaSign.Free (transVar v) noType isaTerm
  --error "No translation for undisambiguated identifier"
transTERM _sign _tr _ =
  error "CASL2IsabelleHOL.transTERM" 


