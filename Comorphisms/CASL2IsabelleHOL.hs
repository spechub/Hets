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
import Common.Id
import Common.AS_Annotation
import qualified Common.Lib.Map as Map
import Common.Lib.Set as Set
import Data.List as List
import Data.Maybe
import Data.Char
import Common.PrettyPrint
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
import Isabelle.Logic_Isabelle
import Isabelle.IsaPrint

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
  Just(IsaSign.Sign{
    baseSig = "Main",
    tsig = emptyTypeSig 
            {tycons = Set.fold (\s -> Map.insert (showIsa s) 0) 
                               Map.empty (sortSet sign)},
    constTab = Map.foldWithKey insertOps
                  (Map.foldWithKey insertPreds
                                   Map.empty
                                   (predMap sign))
                  (opMap sign),
    dataTypeTab = makeDtDefs sign $ sens,
    syn = (), 
    showLemmas = False },
     map (mapNamed (mapSen trForm sign)) sens)  -- for now, no new sentences
  where 
    insertOps op ts m = 
     if Set.size ts == 1 
      then Map.insert (showIsa op) (transOpType (Set.findMin ts)) m
      else
      foldl (\m1 (t,i) -> Map.insert (showIsaI op i) (transOpType t) m1) m 
            (zip (Set.toList ts) [1..size ts])
    insertPreds pred ts m =
     if Set.size ts == 1 
      then Map.insert (showIsa pred) (transPredType (Set.findMin ts)) m
      else
      foldl (\m1 (t,i) -> Map.insert (showIsaI pred i) (transPredType t) m1) m 
            (zip (Set.toList ts) [1..size ts])
 
makeDtDefs :: CASL.Sign.Sign f e -> [Named (FORMULA f)] 
               -> [[(Typ,[(String,[Typ])])]]
makeDtDefs sign = mapMaybe $ makeDtDef sign

makeDtDef :: CASL.Sign.Sign f e -> Named (FORMULA f) -> 
             Maybe [(Typ,[(String,[Typ])])]
makeDtDef sign (NamedSen _ (Sort_gen_ax constrs True)) =
  Just(map makeDt srts)
  where 
  (srts,ops,maps) = recover_Sort_gen_ax constrs
  makeDt s = (transSort s, map makeOp (List.filter (hasSort s) ops))
  makeOp opSym = (transOP_SYMB sign opSym, transArgs opSym)
  hasSort s (Qual_op_name _ ot _) = s == res_OP_TYPE ot 
  hasSort _ _ = error "CASL2IsabelleHOL : hasSort"
  transArgs (Qual_op_name _ ot _) = map transSort $ args_OP_TYPE ot
  transArgs _ = error "CASL2IsabelleHOL : transArgs"
makeDtDef _ _ = Nothing

transSort :: SORT -> Typ
transSort s = Type (showIsa s) [] []

transOpType :: OpType -> Typ
transOpType ot = map transSort (opArgs ot) ---> transSort (opRes ot)

transPredType :: PredType -> Typ
transPredType pt = map transSort (predArgs pt) ---> boolType


------------------------------ Formulas ------------------------------

var :: String -> Term
var v = IsaSign.Free v noType isaTerm

transVar :: VAR -> String
transVar = showIsaSid

xvar :: Int -> String
xvar i = if i<=26 then [chr (i+ord('a'))] else "x"++show i

rvar :: Int -> String
rvar i = if i<=9 then [chr (i+ord('R'))] else "R"++show i

quantifyIsa q (v,t) phi =
  App (Const q noType isaTerm) (Abs (Const v noType isaTerm) t phi NotCont)
      NotCont

quantify q (v,t) phi  = 
  quantifyIsa (qname q) (transVar v, transSort t) phi
  where
  qname Universal = "All"
  qname Existential = "Ex"
  qname Unique_existential = "Ex1"


binOp s phi1 phi2 = 
    App (App (Const s noType isaTerm) phi1 NotCont) phi2 NotCont
binConj= binOp "op &"
conj l = if null l then true else foldr1 binConj l

binDisj = binOp "op |"
binImpl = binOp "op -->"
binEq = binOp "op ="
true = Const "True" noType isaTerm
false = Const "False" noType isaTerm 

prodType t1 t2 = Type "*" [t1,t2] []

transOP_SYMB _ (Op_name op) = error "CASL2Isabelle: unqualified operation"
transOP_SYMB sign (Qual_op_name op ot _) = 
  case (do ots <- Map.lookup op (opMap sign)
           if Set.size ots == 1 then return $ showIsa op
            else do i <- elemIndex (toOpType ot) (Set.toList ots)
                    return $ showIsaI op (i+1)) of
    Just str -> str  
    Nothing -> showIsa op

transPRED_SYMB _ (Pred_name p) = error "CASL2Isabelle: unqualified predicate"
transPRED_SYMB sign (Qual_pred_name p pt _) =
  case (do pts <- Map.lookup p (predMap sign)
           if Set.size pts == 1 then return $ showIsa p 
            else do i <- elemIndex (toPredType pt) (Set.toList pts)
                    return $ showIsaI p (i+1)) of
    Just str -> str
    Nothing -> error "CASL2Isabelle: showIsa p"

mapSen :: FormulaTranslator f e -> CASL.Sign.Sign f e -> FORMULA f -> Sentence
mapSen trFrom sign phi = 
  Sentence {senTerm = transFORMULA sign trFrom (stripQuant phi)}


transFORMULA :: CASL.Sign.Sign f e -> FormulaTranslator f e 
                -> FORMULA f -> Term
transFORMULA sign tr (Quantification quant vdecl phi _) =
  foldr (quantify quant) (transFORMULA sign tr phi) (flatVAR_DECLs vdecl)
transFORMULA sign tr (Conjunction phis _) =
  if null phis then true
  else foldl1 binConj (map (transFORMULA sign tr) phis)
transFORMULA sign tr (Disjunction phis _) =
  if null phis then false
  else foldl1 binDisj (map (transFORMULA sign tr) phis)
transFORMULA sign tr (Implication phi1 phi2 _ _) =
  binImpl (transFORMULA sign tr phi1) (transFORMULA sign tr phi2)
transFORMULA sign tr (Equivalence phi1 phi2 _) =
  binEq (transFORMULA sign tr phi1) (transFORMULA sign tr phi2)
transFORMULA sign tr (Negation phi _) =
  App (Const "Not" noType isaTerm) (transFORMULA sign tr phi) NotCont
transFORMULA sign tr (True_atom _) =
  true
transFORMULA sign tr (False_atom _) =
  false
transFORMULA sign tr (Predication psymb args _) =
  foldl ( \ t1 t2 -> App t1 t2 NotCont)  
            (Const (transPRED_SYMB sign psymb) noType isaTerm) 
            (map (transTERM sign tr) args)
transFORMULA sign tr (Definedness t _) =
  true
transFORMULA sign tr (Existl_equation t1 t2 _) =
  binOp "op =" (transTERM sign tr t1) (transTERM sign tr t2)
transFORMULA sign tr (Strong_equation t1 t2 _) =
  binOp "op =" (transTERM sign tr t1) (transTERM sign tr t2)
transFORMULA sign tr (Membership t1 s _) =
  trace "WARNING: ignoring membership formula" $ true
  --error "No translation for membership"
transFORMULA sign tr (Sort_gen_ax constrs _) =
   trace "WARNING: ignoring sort generation constraints" 
          $ true
  --error "No translation for sort generation constraints"
transFORMULA sign tr (Mixfix_formula _) = 
  error "No translation for mixfix formulas"
transFORMULA sign tr (Unparsed_formula _ _) = 
  error "No translation for unparsed formulas"
transFORMULA sign tr (ExtFORMULA phi) =
  tr sign phi

transTERM sign tr (Qual_var v s _) =
  var $ transVar v
transTERM sign tr (Application opsymb args _) =
  foldl ( \ t1 t2 -> App t1 t2 IsCont) 
            (Const (transOP_SYMB sign opsymb) noType isaTerm) 
            (map (transTERM sign tr) args)
transTERM sign tr (Sorted_term t s _) =
  transTERM sign tr t
transTERM sign tr (Cast t s _) =
  transTERM sign tr t -- ??? Should lead to an error!
transTERM sign tr (Conditional t1 phi t2 _) =
  App (App (App (Const "If" noType isaTerm) (transFORMULA sign tr phi) NotCont)
       (transTERM sign tr t1) NotCont) (transTERM sign tr t2) NotCont
transTERM sign tr (Simple_id v) =
  IsaSign.Free (transVar v) noType isaTerm
  --error "No translation for undisambiguated identifier"
transTERM sign tr (Unparsed_term _ _) =
  error "No translation for unparsed terms"
transTERM sign tr (Mixfix_qual_pred _) =
  error "No translation for mixfix terms"
transTERM sign tr (Mixfix_term _) =
  error "No translation for mixfix terms"
transTERM sign tr (Mixfix_token _) =
  error "No translation for mixfix terms"
transTERM sign tr (Mixfix_sorted_term _ _) =
  error "No translation for mixfix terms"

