{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   This module provides show functions for mixfix errors
-}

module CASL.ShowMixfix (showTerm, showFormula) where

import CASL.AS_Basic_CASL
import Common.Id
import Common.Keywords
{-
mapTerm :: f -> f -> Morphism f e m -> TERM f -> TERM f
mapTerm mf m t = case t of
   Qual_var v s ps -> Qual_var v (mapSrt m s) ps
   Application o ts ps -> let 
       newTs = map (mapTerm mf m) ts
       in Application o newTs ps
   Sorted_term st s ps -> let
       newT = mapTerm mf m st
       in Sorted_term newT s ps
   Cast st s ps -> let
       newT = mapTerm mf m st
       in Cast newT s ps
   Conditional t1 f t2 ps -> let
       t3 = mapTerm mf m t1
       newF = mapSen mf m f
       t4 = mapTerm mf m t2
       in Conditional t3 newF t4 ps 
   _ -> error "mapTerm"

mapSen :: MapSen f e m -> Morphism f e m -> FORMULA f -> FORMULA f
mapSen mf m f = case f of 
   Quantification q vs qf ps -> let
       newF = mapSen mf m qf
       in Quantification q (map (mapVars m) vs) newF ps
   Conjunction fs ps -> let
       newFs = map (mapSen mf m) fs
       in Conjunction newFs ps
   Disjunction fs ps -> let
       newFs = map (mapSen mf m) fs
       in Disjunction newFs ps
   Implication f1 f2 b ps -> let
       f3 = mapSen mf m f1
       f4 = mapSen mf m f2
       in Implication f3 f4 b ps
   Equivalence f1 f2 ps -> let
       f3 = mapSen mf m f1
       f4 = mapSen mf m f2
       in Equivalence f3 f4 ps
   Negation nf ps -> let
       newF = mapSen mf m nf
       in Negation newF ps
   True_atom _ -> f
   False_atom _ -> f
   Predication p ts ps -> let 
       newTs = map (mapTerm mf m) ts
       newP = mapPrSymb m p
       in Predication newP newTs ps
   Definedness t ps -> let 
       newT = mapTerm mf m t
       in Definedness newT ps
   Existl_equation t1 t2 ps -> let
       t3 = mapTerm mf m t1
       t4 = mapTerm mf m t2
       in Existl_equation t3 t4 ps
   Strong_equation t1 t2 ps -> let
       t3 = mapTerm mf m t1
       t4 = mapTerm mf m t2
       in Strong_equation t3 t4 ps
   Membership t s ps -> let 
       newT = mapTerm mf m t
       in Membership newT (mapSrt m s) ps
   Sort_gen_ax constrs isFree -> let
       newConstrs = map (mapConstr m) constrs
       in Sort_gen_ax newConstrs isFree
   ExtFORMULA ef -> let 
       newF = mf m ef 
       in ExtFORMULA newF	       
   _ -> error "mapSen"
-}

bl :: ShowS
bl = showChar ' '

-- | shows Terms fully bracketed for mixfix errors
showTerm :: TERM f -> ShowS
showTerm (Simple_id s)               = showTok s
showTerm (Qual_var v s _ )           = showParen True $ 
    showString varS . bl . showTok v  . showString colonS . showId s
showTerm (Application op_s ts _)     = 
    showOps op_s . if null ts then id else 
	    showFnTs showTerm ts "(" ")" ","
showTerm (Sorted_term t s _)         = 
    showTerm t . bl . showString colonS . showId s
showTerm (Cast t s _)                = 
    showTerm t. bl . showString asS . bl . showId s
showTerm (Conditional t1 f t2 _)     = showTerm t1. bl . showString whenS
                                        . bl . showFormula f. bl
                                        . showString elseS. bl . showTerm t2 
showTerm (Unparsed_term str _)       = showString str
showTerm (Mixfix_qual_pred ps)       = showPredSymb ps
showTerm (Mixfix_term ts)            = showFnTs showTerm ts "" "" " "
showTerm (Mixfix_token t)            = showTok t
showTerm (Mixfix_sorted_term s _ )   = showString colonS . showId s
showTerm (Mixfix_cast s _)           = showString asS . bl . showId s
showTerm (Mixfix_parenthesized ts _) = showFnTs showTerm ts "(" ")" ","
showTerm (Mixfix_bracketed ts _)     = showFnTs showTerm ts "[" "]" ","
showTerm (Mixfix_braced ts _)        = showFnTs showTerm ts "{" "}" ","

-- die show-Funktion fuer den Datentyp OP_Symb
showOps :: OP_SYMB -> ShowS
showOps(Op_name i)              = showId i
showOps(Qual_op_name opn opt _) = showParen True $ showString opS . bl
                                     . showId opn . showString colonS
                                     . showOpt opt

-- die show-Funktion fuer den Datentyp OP_Type
showOpt :: OP_TYPE -> ShowS
showOpt (Op_type k sorts s _ )   = 
    (if null sorts then id
     else showProduct sorts . bl . showString funS)
     . showString (case k of Partial -> quMark
                             _ -> " ") . showId s   

-- die show-Funktion fuer den Daten-Typ FORMULA
showFormula :: FORMULA f -> ShowS
showFormula (Quantification qu var_Ds f _) 
            = showQuantifier qu . bl . showVarDecls var_Ds  
              . showString dotS . showFormula f
showFormula (Conjunction forms _) 
            = showFnTs showFormula forms "(" ")" (" "++lAnd++" ")
showFormula (Disjunction forms _) 
            = showFnTs showFormula forms "(" ")" (" "++lOr++" ")
showFormula (Implication f1 f2 b _) = 
    if b then showFormula f1 . bl . showString implS . bl . showFormula f2
       else showFormula f2 . bl . showString ifS . bl . showFormula f1
showFormula (Equivalence f1 f2 _) = 
    showFormula f1 . bl . showString equivS . bl . showFormula f2
showFormula (Negation f1 _) = 
    showString notS . showParen True (showFormula f1)
showFormula (True_atom _) = showString trueS
showFormula (False_atom _) = showString falseS
showFormula (Predication ps terms _) = showPredSymb ps .
    if null terms then id else showFnTs showTerm terms "(" ")" ","
showFormula (Definedness t _ ) = showString defS . showParen True (showTerm t)
showFormula (Existl_equation t1 t2 _ ) = 
    showTerm t1 . bl . showString exEqual . bl . showTerm t2
showFormula (Strong_equation t1 t2 _ ) = 
    showTerm t1 . bl . showString equalS . bl . showTerm t2
showFormula (Membership t s _ ) = 
    showTerm t . bl . showString inS . bl . showId s
showFormula (Mixfix_formula t ) = showTerm t
showFormula (Unparsed_formula str _ ) = showString str
showFormula (Sort_gen_ax constrs _) = showString generatedS . 
	 showString "{" . showString sortS .
	  showFnTs showId (map newSort constrs) "" "" "," .
	  showString "; ...}"
showFormula (ExtFORMULA _) = showString "(<extended formula>)"

-- die show-Funktion fuer den Datentyp QUANTIFIER
showQuantifier :: QUANTIFIER -> ShowS
showQuantifier Universal = showString forallS
showQuantifier Existential = showString existsS
showQuantifier Unique_existential = showString existsS.showString exMark

showVarDecls :: [VAR_DECL]->ShowS
showVarDecls (vd:[]) = showVarDecl vd
showVarDecls (vd:r)  = showVarDecl vd.showString ";".showVarDecls r
showVarDecls []      = showString ""
 
--Die beiden folgenden Funktionene noch einmal ueberarbeiten
showVarDecl :: VAR_DECL -> ShowS
showVarDecl (Var_decl vars s _) = 
    showFnTs showVar vars "" "" "," . showString colonS . showId s

showVar::VAR -> ShowS
showVar v = showString $ tokStr v

-- show fuer den Datentyp PRED_SYMB
showPredSymb::PRED_SYMB->ShowS
showPredSymb (Pred_name pn)           = showId pn
showPredSymb (Qual_pred_name pn pt _) = showParen True $ 
    showString predS . bl . showId pn . showString colonS . showPredType pt

-- show fuer den Datentyp PRED_TYPE
showPredType::PRED_TYPE->ShowS
showPredType (Pred_type sorts _) = 
    if null sorts then showString "()" else showProduct sorts

showProduct :: [SORT] -> ShowS
showProduct sorts = showFnTs showSort  sorts "" "" prodS

showSort :: SORT -> ShowS
showSort s = showId s 

type LeftKL  = String
type RightKL = String
type Septor  = String

showFnTs :: (a -> ShowS) -> [a] -> LeftKL -> RightKL -> Septor -> ShowS
showFnTs _ [] le ri _ = showString le . showString ri
showFnTs f [x] le ri _ = showString le . f x . showString ri
showFnTs f (x:xs) le ri sep = showString le . f x . showString sep
                              . showFnTs f xs "" "" sep
                              . showString ri
