                                                    
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
-- darf ich das importieren?
--import List

showTerm :: TERM -> String
showTerm (Simple_id s) = tokStr s 
showTerm (Qual_var v s _ ) = tokStr v ++ showId s ""
showTerm (Application op_s ts _) = showOps op_s ++"("++ showTerms ts ++")"
showTerm (Sorted_term t s _) = showTerm t ++ showId s ""
showTerm (Cast t s _) = showTerm t ++ showId s ""
showTerm (Conditional t1 f t2 _) = showTerm t1 ++ showFormula f ++ showTerm t2
showTerm (Unparsed_term str _) = str
-- A new intermediate state
showTerm (Mixfix_qual_pred ps) = showPredSymb ps
showTerm (Mixfix_term terms) = showTerms terms
showTerm (Mixfix_token t) = tokStr t
showTerm (Mixfix_sorted_term s _ ) = showId s ""
showTerm (Mixfix_cast s _) = showId s ""
showTerm (Mixfix_parenthesized ts _) = "("++ showTerms ts ++")"
showTerm (Mixfix_bracketed terms _) = "["++ showTerms terms ++"]"
showTerm (Mixfix_braced terms _) = "{"++ showTerms terms ++"}" 
showTerm t = "Keiner der Faelle ist eingetreten"

-- Achtung: "[" und "]" stehen in der aufrufenden Funktion
showTerms::[TERM] -> String
showTerms ts = if null ts then "" 
	          else showTerms' (reverse ts) ""

showTerms' :: [TERM] -> ShowS
showTerms' (t:ts) y = if null ts then showString (showTerm t) y 
		        else showTerms' ts $ showString (showTerm t) y
--showTerms (t:[]) = showTerm t
--showTerms (t:ts) = showTerm t ++ "," ++ showTerms ts  

{- nur zum Anschauen!!!
neu :: [String]-> String
neu xs = if null xs then ""
                    else neu' (intersperse "," $ reverse xs) "" where
			    neu' (x:r) y = if null r then x ++ y
					     else neu' r x ++ y 
-}
-- die show-Funktion fuer den Datentyp OP_Symb
showOps :: OP_SYMB -> String
showOps(Op_name i) = showId i ""
showOps(Qual_op_name opn opt _) = (showId opn "")++(showOpt opt) 


-- die show-Funktion fuer den Datentyp OP_Type
showOpt :: OP_TYPE -> String
showOpt (Total_op_type sorts s _ )   = showIds sorts ""++showId s ""  
showOpt (Partial_op_type sorts s _ ) = showIds sorts ""++showId s ""

-- die show-Funktion fuer den Daten-Typ FORMULA
showFormula :: FORMULA -> String
showFormula (Quantification qu var_Ds f _) 
             = showQuantifier qu ++ showVDS ++ showFormula f
	       where showVDS = if null var_Ds then "-Fehler?-" 
			          else showVarDecls var_Ds
-- WIE diese Liste von Formeln ausgeben? f1 /\ f2 ?!?
showFormula (Conjunction forms _) = "[f"++ showFormulas forms ++"f]"
-- WIE Liste von Formeln ausgeben? f1 \/ f2
showFormula (Disjunction forms _) = "[f"++ showFormulas forms ++"f]"
-- Ist das Folgende richtig so?
showFormula (Implication f1 f2 _) = showFormula f1 ++ "=>" ++ showFormula f2
showFormula (Equivalence f1 f2 _) = showFormula f1 ++ "<=>" ++ showFormula f2
showFormula (Negation f1 _) = "(neg)"++showFormula f1
showFormula (True_atom _ ) = "True"
showFormula (False_atom _ )= "False"
showFormula (Predication ps terms _) 
             = showPredSymb ps ++ "[t" ++ showTerms terms ++ "t]"
showFormula (Definedness t _ ) = showTerm t
showFormula (Existl_equation t1 t2 _ ) = showTerm t1 ++ "=e=" ++ showTerm t2
showFormula (Strong_equation t1 t2 _ ) = showTerm t1 ++ "=" ++ showTerm t2
showFormula (Membership t s _ ) = showTerm t ++ showId s ""
showFormula (Mixfix_formula t ) = showTerm t
showFormula (Unparsed_formula str _ ) = str

-- eine show-Funktion fuer [FORMULA]
showFormulas :: [FORMULA] -> String
showFormulas forms = if null forms then ""
		        else showFormulas' forms

showFormulas'::[FORMULA] -> String
showFormulas' (f:[]) = showFormula f
showFormulas' (f:fs) = showFormula f ++ "," ++ showFormulas fs

-- die show-Funktion fuer den Datentyp QUANTIFIER
-- ACHTUNG Was soll hier ausgegeben werden? CM fragen!
showQuantifier :: QUANTIFIER -> String
showQuantifier Universal = "QUANTIFIER.Universal"
showQuantifier Existential = "QUANTIFIER.Existential"
showQuantifier Unique_existential = "QUANTIFIER.Unique_existential"

showVarDecls :: [VAR_DECL]->String
showVarDecls vds
    = if null vds then "" 
	 else showVarDecls' vds where
	      showVarDecls' (vd:[]) = showVarDecl vd
	      showVarDecls' (vd:vds)
		  = showVarDecl vd ++ "," ++ showVarDecls vds
   
--Die beiden folgenden Funktionene noch einmal ueberarbeiten
showVarDecl :: VAR_DECL -> String
showVarDecl (Var_decl vars s _ ) = showVars vars ++ showId s ""

-- Show fuer den Datentyp [VAR]==[Token]
-- in der Id.hs gibt es eine Ausgabe. Sollte ich nicht die nehmen?
showVars::[VAR]->String
showVars []   = ""
showVars vars = "[" ++ showVrs vars ++ "]" where
		showVrs (v:[]) = tokStr v
		showVrs (v:vs) = tokStr v ++ "," ++ showVrs vs

-- show fuer den Datentyp PRED_SYMB
showPredSymb::PRED_SYMB->String
showPredSymb (Pred_name pn)           = showId pn ""
showPredSymb (Qual_pred_name pn pt _) = showId pn "" ++ showPredType pt

-- show fuer den Datentyp PRED_TYPE
-- (geht das nicht einfacher?)
showPredType::PRED_TYPE->String
showPredType (Pred_type sorts _) = showIds sorts ""

