                                                    
{- HetCATS/CASL/ShowMixfix.hs
   $Id$
   Author:
   Year:    2002

-}

module CASL.ShowMixfix where

import CASL.AS_Basic_CASL
import Common.Id
import Common.Keywords
import Data.List

showTerm :: TERM -> String
showTerm (Simple_id s)               = tokStr s 
showTerm (Qual_var v s _ )           = "("++varS++ tokStr v ++colonS 
				       ++(showId s "")++")"
showTerm (Application op_s ts _)     = showOps op_s 
                                       ++ if null ts then "" else 
					  showFnTs showTerm ts "(" ")" ","
showTerm (Sorted_term t s _)         = showTerm t ++ colonS ++ showId s ""
showTerm (Cast t s _)                = showTerm t ++ asS ++ showId s ""
showTerm (Conditional t1 f t2 _)     = showTerm t1 ++ whenS 
                                       ++ showFormula f ++ elseS 
                                       ++ showTerm t2
showTerm (Unparsed_term str _)       = str
-- A new intermediate state
showTerm (Mixfix_qual_pred ps)       = showPredSymb ps
showTerm (Mixfix_term ts)            = showFnTs showTerm ts "" "" " "
showTerm (Mixfix_token t)            = tokStr t
showTerm (Mixfix_sorted_term s _ )   = colonS++showId s ""
showTerm (Mixfix_cast s _)           = asS++showId s ""
showTerm (Mixfix_parenthesized ts _) = showFnTs showTerm ts "(" ")" ","
showTerm (Mixfix_bracketed ts _)     = showFnTs showTerm ts "[" "]" ","
showTerm (Mixfix_braced ts _)        = showFnTs showTerm ts "{" "}" ","


-- die show-Funktion fuer den Datentyp OP_Symb
showOps :: OP_SYMB -> String
showOps(Op_name i)              = showId i ""
showOps(Qual_op_name opn opt _) = "("++opS ++ (showId opn "") ++colonS 
                                  ++ (showOpt opt) ++ ")" 

-- die show-Funktion fuer den Datentyp OP_Type
showOpt :: OP_TYPE -> String
showOpt (Total_op_type sorts s _ )   
        = if null sorts then showId s ""
             else showProduct sorts ++ funS ++ showId s ""  
showOpt (Partial_op_type sorts s _ ) 
        = if null sorts then quMark ++ showId s ""
             else showProduct sorts ++ funS ++ quMark 
		      ++ showId s ""

-- die show-Funktion fuer den Daten-Typ FORMULA
showFormula :: FORMULA -> String
showFormula (Quantification qu var_Ds f _) 
            = showQuantifier qu ++ " " ++ showVarDecls var_Ds  
              ++ dotS ++ showFormula f
showFormula (Conjunction forms _) 
            = showFnTs showFormula forms "(" ")" (" "++lAnd++" ")

showFormula (Disjunction forms _) 
            = showFnTs showFormula forms "(" ")" (" "++lOr++" ")

showFormula (Implication f1 f2 _) = showFormula f1 ++ implS  ++ showFormula f2
showFormula (Equivalence f1 f2 _) = showFormula f1 ++ equivS ++ showFormula f2
-- Hier gedanken machen, ob es eein Unterschied ist, ob die Formel eine List oder ein einzelnes Element ist.
showFormula (Negation f1 _) = notS++"("++showFormula f1++")"
showFormula (True_atom _ ) = trueS
showFormula (False_atom _ )= falseS
showFormula (Predication ps terms _) 
             = showPredSymb ps ++ showFnTs showTerm terms  "(" ")" ","
-- Hier gedanken machen, ob es eein Unterschied ist, ob die Formel eine List oder ein einzelnes Element ist.
showFormula (Definedness t _ ) = defS ++"("++showTerm t++")"
showFormula (Existl_equation t1 t2 _ ) = showTerm t1 ++ exEqual ++ showTerm t2
showFormula (Strong_equation t1 t2 _ ) = showTerm t1 ++ equalS ++ showTerm t2
showFormula (Membership t s _ ) = showTerm t ++ inS ++ showId s ""
showFormula (Mixfix_formula t ) = showTerm t
showFormula (Unparsed_formula str _ ) = str

-- die show-Funktion fuer den Datentyp QUANTIFIER
showQuantifier :: QUANTIFIER -> String
showQuantifier Universal = forallS
showQuantifier Existential = existsS
showQuantifier Unique_existential = existsS++exMark

showVarDecls :: [VAR_DECL]->String
showVarDecls (vd:[]) = showVarDecl vd
showVarDecls (vd:r)  = showVarDecl vd ++ ";" ++ showVarDecls r
showVarDecls []      = ""
 
--Die beiden folgenden Funktionene noch einmal ueberarbeiten
showVarDecl :: VAR_DECL -> String
showVarDecl (Var_decl vars s _) 
               = showVars vars ++colonS ++ showId s ""

-- Show fuer den Datentyp [VAR]==[Token]
-- in der Id.hs gibt es eine Ausgabe. Sollte ich nicht die nehmen?
showVars::[VAR]->String
showVars []   = ""
showVars vars = showVars' vars  where
		   showVars' (v:[]) = tokStr v
		   showVars' (v:vs) = tokStr v ++ "," ++ showVars' vs
		   showVars' []     = error "showVars' undefined  for []"

-- show fuer den Datentyp PRED_SYMB
showPredSymb::PRED_SYMB->String
showPredSymb (Pred_name pn)           = showId pn ""
showPredSymb (Qual_pred_name pn pt _) = "("++predS ++ showId pn "" ++ colonS 
                                        ++ showPredType pt ++ ")"

-- show fuer den Datentyp PRED_TYPE
-- (geht das nicht einfacher?)
showPredType::PRED_TYPE->String
showPredType (Pred_type sorts _) = if null sorts then "()" else 
				   showProduct sorts

showProduct :: [SORT] -> String
showProduct sorts = showFnTs showSort  sorts "" "" prodS

showSort :: SORT -> String
showSort s = showId s ""

-- polymorphe Funktion die sowohl showTerms als auch showFormulas ersetzen soll.
-- 
type LeftKL  = String
type RightKL = String
type Septor  = String

showFnTs :: (a -> String) -> [a] -> LeftKL -> RightKL -> Septor -> String
showFnTs _ [] le ri _ = le ++ ri
showFnTs f [x] le ri _ = le ++ f x ++ ri
showFnTs f (x:xs) le ri sep = le ++ f x ++ sep ++ showFnTs f xs "" "" sep ++ ri
