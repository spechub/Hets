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

bl::ShowS
bl = showString " "

-- | shows Terms fully bracketed for mixfix errors
showTerm :: TERM -> ShowS
showTerm (Simple_id s)               = showString (tokStr s) 
showTerm (Qual_var v s _ )           = showParen True (showString varS.bl.
                                                       showString (tokStr v).
                                                       showString colonS.showId s)
showTerm (Application op_s ts _)     = let terms = if null ts then showString "" 
						   else 
					             showFnTs showTerm ts "(" ")" ","
                                       in showOps op_s.terms 
showTerm (Sorted_term t s _)         = showTerm t.showString colonS.showId s
showTerm (Cast t s _)                = showTerm t.bl.showString asS.bl.showId s
showTerm (Conditional t1 f t2 _)     = showTerm t1.bl.showString whenS
                                        .bl.showFormula f.bl
                                        .showString elseS.bl.showTerm t2 
showTerm (Unparsed_term str _)       = showString str
-- A new intermediate state
showTerm (Mixfix_qual_pred ps)       = showPredSymb ps
showTerm (Mixfix_term ts)            = showFnTs showTerm ts "" "" " "
showTerm (Mixfix_token t)            = showString $ tokStr t
showTerm (Mixfix_sorted_term s _ )   = showString colonS.showId s
showTerm (Mixfix_cast s _)           = showString asS.bl.showId s
showTerm (Mixfix_parenthesized ts _) = showFnTs showTerm ts "(" ")" ","
showTerm (Mixfix_bracketed ts _)     = showFnTs showTerm ts "[" "]" ","
showTerm (Mixfix_braced ts _)        = showFnTs showTerm ts "{" "}" ","


-- die show-Funktion fuer den Datentyp OP_Symb
showOps :: OP_SYMB -> ShowS
showOps(Op_name i)              = showId i
showOps(Qual_op_name opn opt _) = showParen True $ showString opS.bl
                                     .showId opn.showString colonS
                                     .showOpt opt

-- die show-Funktion fuer den Datentyp OP_Type
showOpt :: OP_TYPE -> ShowS
showOpt (Total_op_type sorts s _ )   
        = if null sorts then showId s 
             else showProduct sorts.bl.showString funS.bl.showId s   
showOpt (Partial_op_type sorts s _ ) 
        = if null sorts then showString quMark.showId s
             else showProduct sorts.bl.showString funS
                   .showString quMark.showId s

-- die show-Funktion fuer den Daten-Typ FORMULA
showFormula :: FORMULA -> ShowS
showFormula (Quantification qu var_Ds f _) 
            = showQuantifier qu.bl.showVarDecls var_Ds  
              .showString dotS.showFormula f
showFormula (Conjunction forms _) 
            = showFnTs showFormula forms "(" ")" (" "++lAnd++" ")
showFormula (Disjunction forms _) 
            = showFnTs showFormula forms "(" ")" (" "++lOr++" ")
showFormula (Implication f1 f2 _) = showFormula f1.bl.showString implS.bl.showFormula f2
showFormula (Equivalence f1 f2 _) = showFormula f1.bl.showString equivS.bl.showFormula f2
showFormula (Negation f1 _) = showString notS.showParen True (showFormula f1)
showFormula (True_atom _ ) = showString trueS
showFormula (False_atom _ )= showString falseS
showFormula (Predication ps terms _) 
             = showPredSymb ps.shT where 
                  shT = if null terms then showString ""
			   else showFnTs showTerm terms "(" ")" ","
             
-- Hier gedanken machen, ob es eein Unterschied ist, ob die Formel eine List oder ein einzelnes Element ist.
showFormula (Definedness t _ ) = showString defS.showParen True (showTerm t)
showFormula (Existl_equation t1 t2 _ ) = showTerm t1.bl.showString exEqual.bl.showTerm t2
showFormula (Strong_equation t1 t2 _ ) = showTerm t1.bl.showString equalS.bl.showTerm t2
showFormula (Membership t s _ ) = showTerm t.bl.showString inS.bl.showId s
showFormula (Mixfix_formula t ) = showTerm t
showFormula (Unparsed_formula str _ ) = showString str

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
showVarDecl (Var_decl vars s _) 
               = showFnTs showVar vars "" "" ",".showString colonS.showId s

showVar::VAR -> ShowS
showVar v = showString $ tokStr v

-- show fuer den Datentyp PRED_SYMB
showPredSymb::PRED_SYMB->ShowS
showPredSymb (Pred_name pn)           = showId pn
showPredSymb (Qual_pred_name pn pt _) = showParen True $ showString predS
                                         .bl.showId pn.showString colonS
                                         .showPredType pt

-- show fuer den Datentyp PRED_TYPE
showPredType::PRED_TYPE->ShowS
showPredType (Pred_type sorts _) = if null sorts then showString "()" 
				   else showProduct sorts

showProduct :: [SORT] -> ShowS
showProduct sorts = showFnTs showSort  sorts "" "" prodS

showSort :: SORT -> ShowS
showSort s = showId s 

type LeftKL  = String
type RightKL = String
type Septor  = String


showFnTs :: (a -> ShowS) -> [a] -> LeftKL -> RightKL -> Septor -> ShowS
showFnTs _ [] le ri _ = showString le.showString ri
showFnTs f [x] le ri _ = showString le.f x.showString ri
showFnTs f (x:xs) le ri sep = showString le.f x.showString sep
                              .(showFnTs f xs "" "" sep)
                              .showString ri





