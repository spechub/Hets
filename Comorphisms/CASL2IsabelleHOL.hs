{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski and Uni Bremen 2003
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

   
   The embedding comorphism from CASL to Isabelle-HOL.

-}

module Comorphisms.CASL2IsabelleHOL where

import Logic.Logic
import Logic.Comorphism
import Common.Id
import qualified Common.Lib.Map as Map
import Common.Lib.Set as Set
import Data.Dynamic
import Data.List

-- CASL
import CASL.Logic_CASL 
import CASL.AS_Basic_CASL
import CASL.Sublogic
import CASL.Sign
import CASL.Morphism

-- Isabelle
import Isabelle.IsaSign as IsaSign
import Isabelle.Logic_Isabelle

-- | The identity of the comorphism
data CASL2IsabelleHOL = CASL2IsabelleHOL deriving (Show)

instance Language CASL2IsabelleHOL -- default definition is okay

tycon_CASL2IsabelleHOL :: TyCon
tycon_CASL2IsabelleHOL = mkTyCon "G_sign"

instance Typeable CASL2IsabelleHOL where
  typeOf _ = mkAppTy tycon_CASL2IsabelleHOL []

instance Comorphism CASL2IsabelleHOL
               CASL CASL.Sublogic.CASL_Sublogics
               BASIC_SPEC FORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASL.Sign.Sign 
               CASL.Morphism.Morphism
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
    map_sign _ = transSignature
    --map_morphism _ morphism1 -> Maybe morphism2
    map_sentence _ sign phi =
      Just $ Sentence {senTerm = transFORMULA sign phi}
    --map_symbol :: cid -> symbol1 -> Set symbol2

------------------------------ Ids ---------------------------------

-- drop special characters from Ids
transChar :: Char -> String
transChar '[' = "__"
transChar ']' = "__"
transChar x = [x]

transString :: String -> String
transString = concat . map transChar

showIsa :: Id -> String
showIsa = transString . show

showIsaSid :: SIMPLE_ID -> String
showIsaSid = transString . show 

-- disambiguation of overloaded ids
showIsaI :: Id -> Int -> String
showIsaI ident i = showIsa ident ++ "__" ++ show i


---------------------------- Signature -----------------------------

transSignature :: CASL.Sign.Sign -> Maybe(IsaSign.Sign,[IsaSign.Sentence]) 
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
    syn = () },
     [] )  -- for now. no sentences
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
 
transSort :: SORT -> Typ
transSort s = Type(showIsa s,[])

transOpType :: OpType -> Typ
transOpType ot = map transSort (opArgs ot) ---> transSort (opRes ot)

transPredType :: PredType -> Typ
transPredType pt = map transSort (predArgs pt) ---> boolType


------------------------------ Formulas ------------------------------

transVar :: VAR -> String
transVar = showIsaSid

flatVAR_DECL :: VAR_DECL -> [(VAR, SORT)]
flatVAR_DECL (Var_decl vlist s _) = map (\v -> (v,s)) vlist

flatVAR_DECLs :: [VAR_DECL] -> [(VAR, SORT)]
flatVAR_DECLs = concat . map flatVAR_DECL

quantify q (v,t) phi  = 
  Const (qname q,dummyT) `App` Abs (transVar v,transSort t,phi)
  where
  qname Universal = "All"
  qname Existential = "Ex"
  qname Unique_existential = "Ex1"

binConj phi1 phi2 = 
  Const("op &",dummyT) `App` phi1 `App` phi2
binDisj phi1 phi2 = 
  Const("op |",dummyT) `App` phi1 `App` phi2
binImpl phi1 phi2 = 
  Const("op -->",dummyT) `App` phi1 `App` phi2
binEq phi1 phi2 = 
  Const("op =",dummyT) `App` phi1 `App` phi2

transOP_SYMB _ (Op_name op) = showIsa op
transOP_SYMB sign (Qual_op_name op ot _) = 
  case (do ots <- Map.lookup op (opMap sign)
           elemIndex (toOpType ot) (Set.toList ots)) of
    Just i -> showIsaI op i
    Nothing -> showIsa op

transPRED_SYMB _ (Pred_name p) = showIsa p
transPRED_SYMB sign (Qual_pred_name p pt _) =
  case (do pts <- Map.lookup p (predMap sign)
           elemIndex (toPredType pt) (Set.toList pts)) of
    Just i -> showIsaI p i
    Nothing -> showIsa p

transFORMULA :: CASL.Sign.Sign -> FORMULA -> Term
transFORMULA sign (Quantification quant vdecl phi _) =
  foldr (quantify quant) (transFORMULA sign phi) (flatVAR_DECLs vdecl)
transFORMULA sign (Conjunction phis _) =
  foldl1 binConj (map (transFORMULA sign) phis)
transFORMULA sign (Disjunction phis _) =
  foldl1 binDisj (map (transFORMULA sign) phis)
transFORMULA sign (Implication phi1 phi2 _) =
  binImpl (transFORMULA sign phi1) (transFORMULA sign phi2)
transFORMULA sign (Equivalence phi1 phi2 _) =
  binEq (transFORMULA sign phi1) (transFORMULA sign phi2)
transFORMULA sign (Negation phi _) =
  Const ("Not",dummyT) `App` (transFORMULA sign phi)
transFORMULA sign (Negation phi _) =
  Const ("Not",dummyT) `App` (transFORMULA sign phi)
transFORMULA sign (True_atom _) =
  Const ("True",dummyT)
transFORMULA sign (False_atom _) =
  Const ("False",dummyT)
transFORMULA sign (Predication psymb args _) =
  foldl App (Const (transPRED_SYMB sign psymb,dummyT)) 
            (map (transTERM sign) args)
transFORMULA sign (Definedness t _) =
  Const ("True",dummyT)
transFORMULA sign (Existl_equation t1 t2 _) =
  Const ("op =",dummyT) `App` (transTERM sign t1) `App` (transTERM sign t2)
transFORMULA sign (Strong_equation t1 t2 _) =
  Const ("op =",dummyT) `App` (transTERM sign t1) `App` (transTERM sign t2)
transFORMULA sign (Membership t1 s _) =
  error "No translation for membership"
transFORMULA sign (Sort_gen_ax sorts ops) =
  error "No translation for sort generation constraints"
transFORMULA sign (Mixfix_formula _) = 
  error "No translation for mixfix formulas"
transFORMULA sign (Unparsed_formula _ _) = 
  error "No translation for unparsed formulas"

transTERM sign (Qual_var v s _) =
  Free(transVar v,dummyT)
transTERM sign (Application opsymb args _) =
  foldl App (Const (transOP_SYMB sign opsymb,dummyT)) 
            (map (transTERM sign) args)
transTERM sign (Sorted_term t s _) =
  transTERM sign t
transTERM sign (Cast t s _) =
  transTERM sign t
transTERM sign (Conditional t1 phi t2 _) =
  Const ("If",dummyT) `App` (transFORMULA sign phi) 
                      `App` (transTERM sign t1)
                      `App` (transTERM sign t2)
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
transTERM sign (Simple_id _) =
  error "No translation for undisambigated identifier"
