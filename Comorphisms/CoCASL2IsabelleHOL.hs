{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski and Uni Bremen 2003
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

   
   The embedding comorphism from CoCASL to Isabelle-HOL.

-}

module Comorphisms.CoCASL2IsabelleHOL where

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
-- CoCASL
import CoCASL.Logic_CoCASL
import CoCASL.CoCASLSign
import CoCASL.AS_CoCASL
import CoCASL.StatAna
import CASL.Sign
import CASL.AS_Basic_CASL
import CASL.Morphism
import CASL.Quantification 

-- Isabelle
import Isabelle.IsaSign as IsaSign
import Isabelle.Logic_Isabelle
import Isabelle.IsaPrint

-- | The identity of the comorphism
data CoCASL2IsabelleHOL = CoCASL2IsabelleHOL deriving (Show)

instance Language CoCASL2IsabelleHOL -- default definition is okay

instance Comorphism CoCASL2IsabelleHOL
               CoCASL ()
               C_BASIC_SPEC CoCASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CSign 
               CoCASLMor
               CASL.Morphism.Symbol CASL.Morphism.RawSymbol ()
               Isabelle () () IsaSign.Sentence () ()
               IsaSign.Sign 
               () () () ()  where
    sourceLogic _ = CoCASL
    sourceSublogic _ = ()
    targetLogic _ = Isabelle
    targetSublogic _ = ()
    map_sign _ = transSignature
    --map_morphism _ morphism1 -> Maybe morphism2
    map_sentence _ sign phi =
      Just $ Sentence {senTerm = transFORMULA sign (stripQuant phi)}
    --map_symbol :: cid -> symbol1 -> Set symbol2

------------------------------ Ids ---------------------------------


---------------------------- Signature -----------------------------

transSignature :: CSign  
                   -> Maybe(IsaSign.Sign,[Named IsaSign.Sentence]) 
transSignature sign = 
  Just(IsaSign.Sign{
    baseSig = "HOL",
    tsig = emptyTypeSig 
            {tycons = Set.fold (\s -> Map.insert (showIsa s) 0) 
                               Map.empty (sortSet sign)},
    constTab = Map.foldWithKey insertOps
                  (Map.foldWithKey insertPreds
                                   Map.empty
                                   (predMap sign))
                  (opMap sign),
    dataTypeTab = makeDtDefs sign $ sentences sign,
    syn = () },
     [] )  -- for now, no sentences
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
 
makeDtDefs :: CSign -> [Named CoCASLFORMULA] -> [[(Typ,[(String,[Typ])])]]
makeDtDefs sign = mapMaybe $ makeDtDef sign

makeDtDef :: CSign -> Named CoCASLFORMULA -> Maybe [(Typ,[(String,[Typ])])]
makeDtDef sign (NamedSen _ (Sort_gen_ax constrs True)) =
  Just(map makeDt srts)
  where 
  (srts,ops,maps) = recover_Sort_gen_ax constrs
  makeDt s = (transSort s, map makeOp (List.filter (hasSort s) ops))
  makeOp opSym = (transOP_SYMB sign opSym, transArgs opSym)
  hasSort s (Qual_op_name _ ot _) = s == res_OP_TYPE ot 
  hasSort _ _ = error "CoCASL2IsabelleHOL : hasSort"
  transArgs (Qual_op_name _ ot _) = map transSort $ args_OP_TYPE ot
  transArgs _ = error "CoCASL2IsabelleHOL : transArgs"
makeDtDef _ _ = Nothing

transSort :: SORT -> Typ
transSort s = Type(showIsa s,[])

transOpType :: OpType -> Typ
transOpType ot = map transSort (opArgs ot) ---> transSort (opRes ot)

transPredType :: PredType -> Typ
transPredType pt = map transSort (predArgs pt) ---> boolType


------------------------------ Formulas ------------------------------

var :: String -> Term
var v = IsaSign.Free(v,dummyT)

transVar :: VAR -> String
transVar = showIsaSid

xvar :: Int -> String
xvar i = if i<=26 then [chr (i+ord('a'))] else "x"++show i

rvar :: Int -> String
rvar i = if i<=9 then [chr (i+ord('R'))] else "R"++show i

quantifyIsa q (v,t) phi =
  Const (q,dummyT) `App` Abs ( (Const(v, dummyT)) , t,phi)

quantify q (v,t) phi  = 
  quantifyIsa (qname q) (transVar v, transSort t) phi
  where
  qname Universal = "All"
  qname Existential = "Ex"
  qname Unique_existential = "Ex1"

binConj phi1 phi2 = 
  Const("op &",dummyT) `App` phi1 `App` phi2
conj l = if null l then true else foldr1 binConj l

binDisj phi1 phi2 = 
  Const("op |",dummyT) `App` phi1 `App` phi2
binImpl phi1 phi2 = 
  Const("op -->",dummyT) `App` phi1 `App` phi2
binEq phi1 phi2 = 
  Const("op =",dummyT) `App` phi1 `App` phi2
true = Const ("True",dummyT)

prodType t1 t2 = Type("*",[t1,t2])

transOP_SYMB _ (Op_name op) = error "CoCASL2Isabelle: unqualified operation"
transOP_SYMB sign (Qual_op_name op ot _) = 
  case (do ots <- Map.lookup op (opMap sign)
           if Set.size ots == 1 then return $ showIsa op
            else do i <- elemIndex (toOpType ot) (Set.toList ots)
                    return $ showIsaI op (i+1)) of
    Just str -> str  
    Nothing -> showIsa op

transPRED_SYMB _ (Pred_name p) = error "CoCASL2Isabelle: unqualified predicate"
transPRED_SYMB sign (Qual_pred_name p pt _) =
  case (do pts <- Map.lookup p (predMap sign)
           if Set.size pts == 1 then return $ showIsa p 
            else do i <- elemIndex (toPredType pt) (Set.toList pts)
                    return $ showIsaI p (i+1)) of
    Just str -> str
    Nothing -> error "showIsa p"

transFORMULA :: CSign  -> CoCASLFORMULA -> Term
transFORMULA sign (Quantification quant vdecl phi _) =
  foldr (quantify quant) (transFORMULA sign phi) (flatVAR_DECLs vdecl)
transFORMULA sign (Conjunction phis _) =
  foldl1 binConj (map (transFORMULA sign) phis)
transFORMULA sign (Disjunction phis _) =
  foldl1 binDisj (map (transFORMULA sign) phis)
transFORMULA sign (Implication phi1 phi2 _ _) =
  binImpl (transFORMULA sign phi1) (transFORMULA sign phi2)
transFORMULA sign (Equivalence phi1 phi2 _) =
  binEq (transFORMULA sign phi1) (transFORMULA sign phi2)
transFORMULA sign (Negation phi _) =
  Const ("Not",dummyT) `App` (transFORMULA sign phi)
transFORMULA sign (True_atom _) =
  true
transFORMULA sign (False_atom _) =
  Const ("False",dummyT)
transFORMULA sign (Predication psymb args _) =
  foldl App (Const (transPRED_SYMB sign psymb,dummyT)) 
            (map (transTERM sign) args)
transFORMULA sign (Definedness t _) =
  true
transFORMULA sign (Existl_equation t1 t2 _) =
  Const ("op =",dummyT) `App` (transTERM sign t1) `App` (transTERM sign t2)
transFORMULA sign (Strong_equation t1 t2 _) =
  Const ("op =",dummyT) `App` (transTERM sign t1) `App` (transTERM sign t2)
transFORMULA sign (Membership t1 s _) =
  trace "WARNING: ignoring membership formula" $ true
  --error "No translation for membership"
transFORMULA sign (Sort_gen_ax constrs _) =
   trace "WARNING: ignoring sort generation constraints" 
          $ true
  --error "No translation for sort generation constraints"
transFORMULA sign (Mixfix_formula _) = 
  error "No translation for mixfix formulas"
transFORMULA sign (Unparsed_formula _ _) = 
  error "No translation for unparsed formulas"
transFORMULA sign (ExtFORMULA (CoSort_gen_ax sorts ops _)) = 
  foldr (quantifyIsa "ALL") phi predDecls
  where
  phi = prems `binImpl` concls
  indices = [1..length sorts]
  predDecls = zip [rvar i | i<-indices] (map binPred sorts)
  binPred s = let s' = transSort s in [s',s'] ---> boolType
  prems = conj (map prem (zip sorts indices))
  prem (s::SORT,i) = 
    let sels = List.filter 
                (\(Qual_op_name _ t _) -> head (args_OP_TYPE t) == s) ops
        premSel opsymb@(Qual_op_name n t _) =
         let args = tail $ args_OP_TYPE t
             indicesArgs = [1..length args]
             res = res_OP_TYPE t
             varDecls = zip [xvar i | i<-indicesArgs] (map transSort args)
             top = Const (transOP_SYMB sign opsymb,dummyT)
             rhs = foldl App (top `App` var "x") (map (var . xvar) indicesArgs)
             lhs = foldl App (top `App` var "y") (map (var . xvar) indicesArgs)
             chi = if res `elem` sorts
                     then var (rvar (fromJust (findIndex (==res) sorts)))
                           `App` rhs `App` lhs
                     else binEq rhs lhs
          in foldr (quantifyIsa "ALL") chi varDecls
        prem1 = conj (map premSel sels)
        concl1 = var (rvar i) `App` var "x" `App` var "y"
        psi = prem1 `binImpl` concl1
        typS = transSort s
     in foldr (quantifyIsa "ALL") psi [("x",typS),("y",typS)]
  concls = conj (map concl (zip sorts indices))
  concl (s,i::Int) = binEq (var (rvar i)) (Const("op =",dummyT))
transFORMULA sign (ExtFORMULA (Box mod phi _)) = 
   trace "WARNING: ignoring modal forumla" 
          $ true
transFORMULA sign (ExtFORMULA (Diamond mod phi _)) = 
   trace "WARNING: ignoring modal forumla" 
          $ true


transTERM sign (Qual_var v s _) =
  var $ transVar v
transTERM sign (Application opsymb args _) =
  foldl App (Const (transOP_SYMB sign opsymb,dummyT)) 
            (map (transTERM sign) args)
transTERM sign (Sorted_term t s _) =
  transTERM sign t
transTERM sign (Cast t s _) =
  transTERM sign t  -- ??? Should lead to an error!
transTERM sign (Conditional t1 phi t2 _) =
  Const ("If",dummyT) `App` (transFORMULA sign phi) 
                      `App` (transTERM sign t1)
                      `App` (transTERM sign t2)
transTERM sign (Simple_id v) =
  var $ transVar v
  --error "No translation for undisambigated identifier"
transTERM sign (Unparsed_term _ _) =
  error "No translation for unparsed terms"
transTERM sign (Mixfix_qual_pred _) =
  error "No translation for mixfix terms"
transTERM sign (Mixfix_term _) =
  error "No translation for mixfix terms"
transTERM sign (Mixfix_token _) =
  error "No translation for mixfix terms"
transTERM sign (Mixfix_sorted_term _ _) =
  error "No translation for mixfix terms"


