                                                    
{- HetCATS/CASL/ShowMixfix.hs
   $Id$
   Author:
   Year:    2002

-}

module CASL.ShowMixfix where

import CASL.AS_Basic_CASL
import CASL.Formula
import Common.Lib.Parsec
import Common.AnnoState
import Common.Id

import List

showTerm :: TERM -> String
showTerm (Simple_id s)               = tokStr s 
showTerm (Qual_var v s _ )           = tokStr v ++ showId s ""
showTerm (Application op_s ts _)     = showOps op_s 
                                       ++ showTerms ts ("(",")")
showTerm (Sorted_term t s _)         = showTerm t ++ " : " ++ showId s ""
showTerm (Cast t s _)                = showTerm t ++ " as " ++ showId s ""
showTerm (Conditional t1 f t2 _)     = showTerm t1 ++ " when " 
                                       ++ showFormula f ++ " else " 
                                       ++ showTerm t2
showTerm (Unparsed_term str _)       = str
-- A new intermediate state
showTerm (Mixfix_qual_pred ps)       = showPredSymb ps
showTerm (Mixfix_term ts)            = showTerms ts ("(",")")
showTerm (Mixfix_token t)            = tokStr t
showTerm (Mixfix_sorted_term s _ )   = showId s ""
showTerm (Mixfix_cast s _)           = showId s ""
showTerm (Mixfix_parenthesized ts _) = showTerms ts ("(",")")
showTerm (Mixfix_bracketed ts _)     = showTerms ts ("[","]")
showTerm (Mixfix_braced ts _)        = showTerms ts ("{","}") 

-- Das zweite Argument ist die Art der Klammer die um die Terme 
-- gepackt werden sollen
showTerms::[TERM] -> (String,String) -> String
showTerms []     _ = "" 
showTerms (t:[]) _ = showTerm t 
showTerms ts     x = fst x ++ showTerms' ts ++ snd x where
		     showTerms' (t:[]) = showTerm t
		     showTerms' (t:r)  = showTerm t ++ "," ++ showTerms' r
		     showTerms' []     = error "showTerms' undefined for []"

-- die show-Funktion fuer den Datentyp OP_Symb
showOps :: OP_SYMB -> String
showOps(Op_name i)              = showId i ""
showOps(Qual_op_name opn opt _) = "( op " ++ (showId opn "")++ " : " 
                                  ++ (showOpt opt) ++ ")" 

-- die show-Funktion fuer den Datentyp OP_Type
showOpt :: OP_TYPE -> String
showOpt (Total_op_type sorts s _ )   
        = if null sorts then showId s ""
             else showIds sorts "" ++ " -> " ++ showId s ""  
showOpt (Partial_op_type sorts s _ ) 
        = if null sorts then "? " ++ showId s ""
             else  showIds sorts ""++ " -> ? " ++ showId s ""

-- die show-Funktion fuer den Daten-Typ FORMULA
showFormula :: FORMULA -> String
showFormula (Quantification qu var_Ds f _) 
            = showQuantifier qu ++ " " ++ showVarDecls var_Ds  
              ++ "." ++ showFormula f
showFormula (Conjunction forms _) 
            = if null forms then ""
		 else "[" ++ (showFormulas forms "/\\") ++ "]"
showFormula (Disjunction forms _) 
            = if null forms then ""
                 else "[" ++ (showFormulas forms "\\/") ++ "]"
showFormula (Implication f1 f2 _) = showFormula f1 ++ " => "  ++ showFormula f2
showFormula (Equivalence f1 f2 _) = showFormula f1 ++ " <=> " ++ showFormula f2
showFormula (Negation f1 _) = "not "++showFormula f1
showFormula (True_atom _ ) = "true "
showFormula (False_atom _ )= "false "
showFormula (Predication ps terms _) 
             = showPredSymb ps ++ showTerms terms  ("[","]")
showFormula (Definedness t _ ) = "def " ++ showTerm t
showFormula (Existl_equation t1 t2 _ ) = showTerm t1 ++ " =e= " ++ showTerm t2
showFormula (Strong_equation t1 t2 _ ) = showTerm t1 ++ " = " ++ showTerm t2
showFormula (Membership t s _ ) = showTerm t ++ " in " ++ showId s ""
showFormula (Mixfix_formula t ) = showTerm t
showFormula (Unparsed_formula str _ ) = str

-- eine show-Funktion fuer [FORMULA]
-- zweites Argument: Disjunction oder Conjunction
showFormulas :: [FORMULA] -> String -> String
showFormulas (f:[]) _ = showFormula f
showFormulas (f:fs) x = showFormula f ++ x ++ showFormulas fs x
showFormulas []     _ = error "showFormulas undefined for []"

-- die show-Funktion fuer den Datentyp QUANTIFIER
showQuantifier :: QUANTIFIER -> String
showQuantifier Universal = "forall"
showQuantifier Existential = "exists"
showQuantifier Unique_existential = "exists!"

showVarDecls :: [VAR_DECL]->String
showVarDecls (vd:[]) = showVarDecl vd
showVarDecls (vd:r)  = showVarDecl vd ++ ";" ++ showVarDecls r
showVarDecls []      = ""
 
--Die beiden folgenden Funktionene noch einmal ueberarbeiten
showVarDecl :: VAR_DECL -> String
showVarDecl (Var_decl vars s _) 
               = showVars vars ++" : " ++ showId s ""

-- Show fuer den Datentyp [VAR]==[Token]
-- in der Id.hs gibt es eine Ausgabe. Sollte ich nicht die nehmen?
showVars::[VAR]->String
showVars []   = ""
showVars vars = showVrs vars  where
		   showVrs (v:[]) = tokStr v
		   showVrs (v:vs) = tokStr v ++ "," ++ showVrs vs
		   showVrs []     = error "showVrs undefined  for []"

-- show fuer den Datentyp PRED_SYMB
showPredSymb::PRED_SYMB->String
showPredSymb (Pred_name pn)           = showId pn ""
showPredSymb (Qual_pred_name pn pt _) = "( pred " ++ showId pn "" ++ " : " 
                                        ++ showPredType pt ++ ")"

-- show fuer den Datentyp PRED_TYPE
-- (geht das nicht einfacher?)
showPredType::PRED_TYPE->String
showPredType (Pred_type sorts _) = if null sorts then "( )"
                                      else showIds sorts ""

