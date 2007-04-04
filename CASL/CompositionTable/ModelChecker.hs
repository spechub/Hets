{- |
Module      :  $Header$
Copyright   :  (c) Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  fmossa@tzi.de
Stability   :  provisional
Portability :  non-portable

Checks validity of Models regarding a composition table
-}

module CASL.CompositionTable.ModelChecker where

import CASL.CompositionTable.CompositionTable
import CASL.AS_Basic_CASL
import CASL.Sign
import Common.AS_Annotation
import Common.Result
import Common.Id
import qualified Data.Map as Map
import qualified Data.Set as Set
import Maybe
import List
import Common.DocUtils


modelCheck :: Pretty f => SIMPLE_ID -> (Sign f e, [Named (FORMULA f)]) -> Table -> Result
	      Bool


modelCheck _ (_,[]) _ = (warning True "nicht implementiert" (Range []))
modelCheck _ ((Sign _ _ _ _ _ _ _ _ ann _ _),sent) t = modelCheckTest
						       (extractAnnotations ann)
						       sent t

extractAnnotations :: Map.Map Symbol (Set.Set Annotation) -> [(OP_SYMB, String)]				   

extractAnnotations m = catMaybes [(extractAnnotation (a,b)) | (a,b) <- (Map.toList m)]
			   


extractAnnotation :: (Symbol, Set.Set Annotation) ->Maybe (OP_SYMB, String)

extractAnnotation ((Symbol symbname symbtype),set) = 
	do
		case symbtype of 
		     OpAsItemType _ -> Just((createOpSymb symbname symbtype), 
					    (getAnno set))  
		     PredAsItemType _ -> Nothing
		     SortAsItemType ->  Nothing
							

createOpSymb :: Id -> SymbType -> OP_SYMB

createOpSymb i (OpAsItemType (OpType op_Kind op_Args op_Res)) =
                 (Qual_op_name i (Op_type op_Kind op_Args op_Res (Range [])) 
		 (Range []))
createOpSymb _ s = error("Aymbtype not supported:"++show(s))
  
getAnno :: Set.Set Annotation -> String
getAnno a  
 | Set.size a == 1 = (getAnno_ (Set.findMin a))
 | otherwise = "failure"

getAnno_:: Annotation -> String 
getAnno_ (Unparsed_anno (Annote_word word) _ _) = word 
getAnno_ _ = []


modelCheckTest :: Pretty f => [(OP_SYMB, String)] -> [Named (FORMULA f)] -> Table -> Result Bool

modelCheckTest _ [] _ = error("no Formulas provided in modelCheckTest")

modelCheckTest symbs [x] t = modelCheckTest_ x t symbs

modelCheckTest a (x:xs) t = do modelCheckTest a xs t
			       modelCheckTest a [x] t 

modelCheckTest_ :: Pretty f => Named (FORMULA f) -> Table -> [(OP_SYMB,String)] -> 
		   Result Bool

modelCheckTest_ (SenAttr _ _ _ _ (Conjunction formulas range)) t symbs
		= let varass = Variable_Assignment []
		      res = and [calculateFormula formula varass t 
				 symbs | formula <- formulas]
                  in if res then return True 
    		            else (warning False ("Conjunction does not hold:" 
						 ++ showDoc(formulas) "") range)

modelCheckTest_ (SenAttr _ _ _ _ (Disjunction formulas range)) t symbs 
		= let varass = Variable_Assignment []
		      res = or [calculateFormula formula varass t 
				 symbs | formula <- formulas]
                  in if res then return True 
    		            else (warning False ("Disjunction does not hold:" 
						 ++ showDoc(formulas) "") range)
modelCheckTest_ (SenAttr _ _ _ _ (Implication f1 f2 _ range)) t symbs 
		= let varass = Variable_Assignment []
                      test1 = calculateFormula f1 varass t symbs
		      test2 = calculateFormula f2 varass t symbs
		      res = not ((test1) && (not test2))
	          in if res then return True
                     else (warning False ("Implication does not hold: f1 is" ++
					  showDoc(f1) "" ++ "f2 is " ++ 
					  showDoc(f2) "")range)		    
 
modelCheckTest_ (SenAttr _ _ _ _ (Equivalence f1 f2 range)) t symbs 
		= let varass = Variable_Assignment []
		      test1 = calculateFormula f1 varass t symbs
		      test2 = calculateFormula f2 varass t symbs
		      res = test1 == test2	      
		 in  if res then return True
                     else (warning False ("Equivalence does not hold: f1 is" ++
					  showDoc(f1) "" ++ "f2 is " ++ 
					  showDoc(f2) "")range)	
		  

modelCheckTest_ (SenAttr _ _ _ _ (Negation f range)) t symbs 
		= let varass = Variable_Assignment []
		      res = calculateFormula f varass t symbs
                  in if (not res) then return True
		                  else (warning False ("Negation does not hold:" 
						 ++ showDoc(f) "") range)
modelCheckTest_ (SenAttr _ _ _ _ (Predication _ _ _)) _ _ 
		= error("not implemented Predication")
modelCheckTest_ (SenAttr _ _ _ _ (Existl_equation _ _ _)) _ _ 
		= error("not implemented Existl_equation")
modelCheckTest_ (SenAttr _ _ _ _ (True_atom _)) _ _ 
		= return True
modelCheckTest_ (SenAttr _ _ _ _ (False_atom range)) _ _ 
		= (warning False "False-atom cant be fulfilled!" range)
modelCheckTest_ (SenAttr _ _ _ _ (Definedness _ _)) _ _ 
		= error("not implemented Definedness")

modelCheckTest_ (SenAttr _ _ _ _ (Strong_equation t1 t2 range)) t symbs 
		= let varass = Variable_Assignment []
		      res1 = calculateTerm t1 varass t symbs
		      res2 = calculateTerm t2 varass t symbs
		      equal = ((subsumes res1 res2) && (subsumes res2 res1))
		  in if equal then return True
		     else (warning False 
				  ("Strong Equation does not hold term1:" 
				  ++ (showDoc t1 "") ++ 
				  "term2:"++(showDoc t2 "")) range) 
modelCheckTest_ (SenAttr _ _ _ _ (Mixfix_formula _)) _ _ 
		= error("not implemented Mixfix_formula")
modelCheckTest_ (SenAttr _ _ _ _ (Sort_gen_ax _ _)) _ _ 
		= error("not implemented Sort_gen_ax")
modelCheckTest_ (SenAttr _ _ _ _ (ExtFORMULA _)) _ _ 
		= error("not implemented ExtFormula" )  
modelCheckTest_ (SenAttr _ _ _ _ (Unparsed_formula _ _)) _ _ 
		= error("not implemented Unparsed_formula" )
modelCheckTest_ (SenAttr _ _ _ _ (Quantification q decl f _)) t
		symbs 
		= calculateQuantification q 
		  (generateVariableAssignments decl t) f t symbs
								     
modelCheckTest_ (SenAttr _ _ _ _ e) _ _ 
		= error("not implemented" ++ show(e) )


calculateQuantification :: Pretty f => QUANTIFIER -> [VARIABLE_ASSIGNMENT] -> 
			   (FORMULA f) -> Table -> [(OP_SYMB,String)]
			   -> Result Bool

calculateQuantification Universal vardecls f t symbs 
			= calculateQuantificationUniversal vardecls f t symbs

calculateQuantification Existential _ _ _ _ 
			= error("not implemented existential")

calculateQuantification Unique_existential _ _ _ _ 
                        = error("not implemented Unique_existential ")


calculateQuantificationUniversal :: Pretty f => [VARIABLE_ASSIGNMENT] -> 
				    (FORMULA f) -> Table -> 
				    [(OP_SYMB,String)] -> Result Bool

calculateQuantificationUniversal [] _ _ _ 
				 = (warning False 
				 "Error: Empty VarAssignment" (Range []))
calculateQuantificationUniversal [x] f t symbs = 
				 let res = calculateFormula
					   f x t symbs
				 in 
				 if (res == True) then return True
				 else (warning False ("universal "++
				      "Quantifier not fulfilled"
				       ++ showDoc f "" ++ "\n" ++ show
				       x) (Range []))    
calculateQuantificationUniversal (x:xs) f t symbs 
				 = do calculateQuantificationUniversal [x] 
				       f t symbs 
				      calculateQuantificationUniversal 
				       xs f t symbs

data VARIABLE_ASSIGNMENT = Variable_Assignment [(VAR,Baserel)]
			   deriving (Show,Eq) 

calculateTerm :: Pretty f => (TERM f) -> VARIABLE_ASSIGNMENT -> Table ->
		 [(OP_SYMB,String)] -> [Baserel]

calculateTerm (Simple_id var) ass _ _
	       = getBaseRelsForVariable var ass
calculateTerm (Qual_var var _ _) ass _ _ = 
               getBaseRelsForVariable var ass
calculateTerm (Application opSymb terms _) ass t symbs =
	      applyOperation (getIdentifierForSymb opSymb symbs) terms
	      t ass symbs

calculateTerm (Sorted_term term _ _) ass t symbs = calculateTerm term
	      ass t symbs

calculateTerm (Cast _ _ _) _ _ _ = error("not implemented Cast")

-- wenn formula = true -> term1 sonst term2
calculateTerm (Conditional t1 fo t2 _) ass t symbs = 
              let res = calculateFormula fo ass t symbs
              in if res then (calculateTerm t1 ass t symbs)
		 else calculateTerm t2 ass t symbs


calculateTerm _ _ _ _ = []

getIdentifierForSymb :: OP_SYMB -> [(OP_SYMB,String)] -> String

getIdentifierForSymb _ [] = ""
getIdentifierForSymb symb [(symb2,s )] | symb == symb2 = s
				       | otherwise = ""
getIdentifierForSymb symb (x:xs)   | (getIdentifierForSymb symb [x]) == "" 
				     = (getIdentifierForSymb symb xs)
				   | otherwise = (getIdentifierForSymb symb [x])
				       

applyOperation :: Pretty f => String -> [(TERM f)] -> Table 
		  -> VARIABLE_ASSIGNMENT -> [(OP_SYMB,String)]-> [Baserel]


applyOperation "RA_zero" [] _ _ _ = []
applyOperation "RA_one" _ (Table (Table_Attrs _ _ baserels)
	      _ _ _ _) _ _ = baserels
applyOperation "RA_intersection" terms table ass symbs = intersect 
	      (calculateTerm (head terms) ass table symbs)
	      (calculateTerm (head (tail terms)) ass table symbs)  
applyOperation "RA_composition" terms (Table attrs 
	      (Compositiontable cmpentries) convtbl refltbl models) 
	      ass symbs = calculateComposition cmpentries
	      (calculateTerm (head terms) ass (Table attrs
	      (Compositiontable cmpentries) convtbl refltbl models) symbs)
	      (calculateTerm (head (tail terms)) ass (Table attrs 
	      (Compositiontable cmpentries) convtbl refltbl models) symbs)
applyOperation "RA_union" terms table ass symbs = union 
	      (calculateTerm (head terms) ass table symbs)
	      (calculateTerm (head(tail terms)) ass table symbs)
applyOperation "RA_complement" terms (Table (Table_Attrs name id_
	       baserels) comptbl convtbl refltbl models) ass symbs = 
	       complement
	       (calculateTerm (head terms) ass (Table (Table_Attrs
	       name id_ baserels) comptbl convtbl refltbl models)
	       symbs) baserels
applyOperation "RA_identity" _ (Table (Table_Attrs _ id_ _)
	       _ _ _ _) _ _ = [id_] 
applyOperation "RA_converse" terms (Table attrs cmptable cnvtable
	       refltbl models)ass symbs = calculateConverse cnvtable 
	       (calculateTerm
	       (head terms) ass (Table attrs cmptable cnvtable refltbl models)
	       symbs) 

applyOperation "RA_shortcut" terms (Table attrs comptbl 
		(Conversetable_Ternary inv shortc hom) refltbl
		models) ass symbs = calculateConverseTernary shortc
		(calculateTerm (head terms) ass (Table attrs comptbl 
		(Conversetable_Ternary inv shortc hom) refltbl
		models) symbs) 
applyOperation "RA_inverse" terms (Table attrs comptbl 
		(Conversetable_Ternary inv shortc hom) refltbl
		models) ass symbs = calculateConverseTernary inv
		(calculateTerm (head terms) ass (Table attrs comptbl 
		(Conversetable_Ternary inv shortc hom) refltbl
		models) symbs)  

applyOperation "RA_homing" terms (Table attrs comptbl 
		(Conversetable_Ternary inv shortc hom) refltbl
		models) ass symbs = calculateConverseTernary hom
		(calculateTerm (head terms) ass (Table attrs comptbl 
		(Conversetable_Ternary inv shortc hom) refltbl
		models) symbs) 
applyOperation _ _ _ _ _ = []


complement :: [Baserel] -> [Baserel] -> [Baserel]
complement rels baserles = baserles \\ rels

calculateComposition :: [Cmptabentry] -> [Baserel] -> [Baserel] ->
			[Baserel]

calculateComposition [] _ _ = []
calculateComposition [x] rels1 rels2 = calculateComposition_ x rels1 rels2
calculateComposition (x:xs) rels1 rels2 = calculateComposition_ x
		     rels1 rels2 ++ calculateComposition xs rels1 rels2

calculateComposition_ :: Cmptabentry -> [Baserel] -> [Baserel] -> [Baserel]

calculateComposition_ (Cmptabentry (Cmptabentry_Attrs rel1 rel2) baserels)
		      rels1 rels2 
		      | (rel1 `elem` rels1 ) && (rel2 `elem` rels2 ) =
		      baserels
		      | otherwise = []

calculateConverse:: Conversetable -> [Baserel] -> [Baserel]

calculateConverse (Conversetable_Ternary _ _ _) _ = [] 
calculateConverse (Conversetable []) _ = [] 
calculateConverse (Conversetable [(Contabentry rel1 rel2)]) rels 
		  | rel1 `elem` rels = [rel2]
		  | otherwise = []
calculateConverse (Conversetable (x:xs)) rels = (calculateConverse 
		  (Conversetable [x]) rels) ++ (calculateConverse
		  (Conversetable xs) rels)


calculateConverseTernary :: [Contabentry_Ternary] -> [Baserel] ->
			    [Baserel]
calculateConverseTernary [] _ = []
calculateConverseTernary [(Contabentry_Ternary rel1 rels1)] rels2 
			  | rel1 `elem` rels2 = rels1
			  | otherwise = []
calculateConverseTernary (x:xs) rels = calculateConverseTernary [x]
				       rels ++
				       calculateConverseTernary xs rels
  

getBaseRelsForVariable :: VAR -> VARIABLE_ASSIGNMENT ->[Baserel]

getBaseRelsForVariable _ (Variable_Assignment []) = []
getBaseRelsForVariable v (Variable_Assignment [(var,baserel)]) 
			 | v == var = [baserel]
			 | otherwise = []  
getBaseRelsForVariable v (Variable_Assignment (x:xs)) = 
		       getBaseRelsForVariable v (Variable_Assignment [x]) ++
		       getBaseRelsForVariable v (Variable_Assignment xs)


calculateFormula ::  Pretty f =>(FORMULA f) -> VARIABLE_ASSIGNMENT -> Table -> 
		    [(OP_SYMB,String)] -> Bool

calculateFormula (Quantification q vardecls f _) varass t symbs = 
		 let (Result _ res) = (calculateQuantification q 
				       (appendVariableAssignments
				       [varass] vardecls t) f t symbs)
		 in 
		  (res == Just True) 
calculateFormula (Conjunction formulas _) varass t symbs = 
		 and [calculateFormula x varass t 
		     symbs | x<-formulas]
	        
calculateFormula (Disjunction formulas _) varass t symbs = 
		 or [calculateFormula x varass t 
		    symbs | x<-formulas]
calculateFormula (Implication f1 f2 _ _) varass t symbs =
		 let test1 = calculateFormula f1 varass t symbs
		     test2 = calculateFormula f2 varass t symbs
		 in 
		  not ((test1) && (not test2)) 
		 
calculateFormula (Equivalence f1 f2 _) varass t symbs =
		 let test1 = calculateFormula f1 varass t symbs
		     test2 = calculateFormula f2 varass t symbs
		 in
		  test1 == test2

calculateFormula (Negation f _) varass t symbs = 
		 not (calculateFormula f varass t symbs)
calculateFormula (True_atom _) _ _ _ = True 
		 
calculateFormula (False_atom _) _ _ _ = False
		
calculateFormula (Predication _ _ _) _ _ _ = 
		 error "not implemented predication" 
		 
calculateFormula (Definedness _ _) _ _ _ = 
		 error "not implemented definedness"
calculateFormula (Existl_equation _ _ _) _ _ _ = 
		 error "not implemented existl"
calculateFormula (Strong_equation term1 term2 _) varass t symbs =
		 let t1 = calculateTerm term1 varass t symbs
		     t2 = calculateTerm term2 varass t symbs
		 in if(((subsumes t1 t2) && (subsumes t2 t1))) then True
		    else False
   
		 
calculateFormula (Membership _ _ _) _ _ _ = 
		 error "not implemented Membership"
calculateFormula (Unparsed_formula _ _) _ _ _ = 
		 error "not implemented unparsed"
calculateFormula (Mixfix_formula _) _ _ _ = 
		 error "not implemented mixfix"
calculateFormula _ _ _ _ = error "not implemented" 

subsumes :: [Baserel] -> [Baserel] -> Bool
subsumes _ [] = True
subsumes [] _ = False
subsumes (x:xs) [y] = x==y || (subsumes xs [y])
subsumes x (y:ys) = (subsumes x [y]) && (subsumes x ys)   

generateVariableAssignments :: [VAR_DECL] -> Table -> [VARIABLE_ASSIGNMENT]

generateVariableAssignments vardecls t = generateVariableAssignments_ (getVars vardecls) t

generateVariableAssignments_:: [VAR] -> Table -> [VARIABLE_ASSIGNMENT]

generateVariableAssignments_ vars t = map Variable_Assignment
				      (appendAssignments [] vars 
				      (getBaseRelations t))  



appendAssignments :: [[(VAR,Baserel)]] -> [VAR] -> [Baserel] ->
		     [[(VAR,Baserel)]]
appendAssignments _ _ [] = []
appendAssignments tuples [] _ = tuples

appendAssignments tuples (x:xs) baserels = appendAssignments
					   (appendAssignments_ tuples x
					   baserels)   xs
					   baserels   


appendAssignments_ :: [[(VAR,Baserel)]] -> VAR -> [Baserel] ->
		     [[(VAR,Baserel)]]
appendAssignments_ [x] var baserels = appendAssignmentSingle x var baserels 
appendAssignments_ [] var baserels = appendAssignmentSingle [] var baserels
appendAssignments_ (x:xs) var baserels = appendAssignmentSingle x var
					 baserels ++ 
					 appendAssignments_
					 xs var baserels


appendAssignmentSingle:: [(VAR,Baserel)] -> VAR -> [Baserel] -> 
			 [[(VAR,Baserel)]]
appendAssignmentSingle _ _ [] = [] 
appendAssignmentSingle assignment var (x:xs) = [( (var,x) : assignment )]
					       ++
					       appendAssignmentSingle 
					       assignment var xs

getVars:: [VAR_DECL] -> [VAR]

getVars [] = [] 
getVars [(Var_decl vars _ _)] = vars
getVars (x:xs) = (getVars [x]) ++ (getVars xs) 

getBaseRelations:: Table -> [Baserel]
getBaseRelations (Table (Table_Attrs _ _ br) _ _ _ _) = br

appendVariableAssignments :: [VARIABLE_ASSIGNMENT] -> [VAR_DECL] -> Table -> [VARIABLE_ASSIGNMENT]
appendVariableAssignments vars decls t = vars ++ (generateVariableAssignments decls t)
 
