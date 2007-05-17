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
import CASL.Logic_CASL
import Logic.Logic
import CASL.ToDoc
import Control.Monad
import Debug.Trace



modelCheck :: SIMPLE_ID -> (Sign () (), [Named (FORMULA ())]) -> 
	      Table -> Result Bool


modelCheck _ (_,[]) _ = (warning True "nicht implementiert" (Range []))
modelCheck _ (sign,sent) t = modelCheckTest  
			     (extractAnnotations (annoMap sign)) (sign,sent) t

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
createOpSymb _ s = error("Symbtype not supported:"++show(s))
  
getAnno :: Set.Set Annotation -> String
getAnno a  
 | Set.size a == 1 = (getAnno_ (Set.findMin a))
 | otherwise = "failure"

getAnno_ :: Annotation -> String 
getAnno_ (Unparsed_anno (Annote_word word) _ _) = word 
getAnno_ _ = []

showDiagStrings:: [Diagnosis] -> [Char]

showDiagStrings [] = []
showDiagStrings ((Diag k s p):xs) = s ++"\n" ++ showDiagStrings xs

modelCheckTest ::  [(OP_SYMB, String)] -> 
		   (Sign () (), [Named (FORMULA ())]) -> Table -> Result Bool

modelCheckTest _ (_,[]) _ = error("no Formulas provided in modelCheckTest")

modelCheckTest symbs (sign,[x]) t = let Result d res = modelCheckTest_ 
						       (sign,x) t symbs
				    in if(length d == 0) then (hint True 
						  ("Formula succeeded: "++show(printTheoryFormula(mapNamed (simplify_sen CASL sign) x))++"\n" ) nullRange)
				        else do (warning False ("Formula failed: \n"++show(printTheoryFormula(mapNamed (simplify_sen CASL sign) x))++"\n some Counterexamples: \n" ++ showDiagStrings(take 10 d) ) nullRange)
--					        Result (take 10 d) (Just False)   
 

modelCheckTest a (sign,(x:xs)) t = do modelCheckTest a (sign, xs) t
			              modelCheckTest a (sign, [x]) t 

modelCheckTest_ :: (Sign () (), Named (FORMULA ())) -> Table -> 
		    [(OP_SYMB,String)] -> Result Bool

modelCheckTest_ (sign, (SenAttr _ _ _ _ (Conjunction formulas range))) t symbs
		= let varass = Variable_Assignment []
		      res = and [calculateFormula (sign,formula) varass t 
				 symbs | formula <- formulas]
                  in if res then return True 
    		            else (warning False ("Conjunction does not hold:" 
						 ++ showDoc(map (simplify_sen CASL sign) formulas) "") range)

modelCheckTest_ (sign, (SenAttr _ _ _ _ (Disjunction formulas range))) t symbs 
		= let varass = Variable_Assignment []
		      res = or [calculateFormula (sign,formula) varass t 
				 symbs | formula <- formulas]
                  in if res then return True 
    		            else (warning False ("Disjunction does not hold:" 
						 ++ showDoc((map (simplify_sen 
						 CASL sign) formulas)) "") range)
modelCheckTest_ (sign, (SenAttr _ _ _ _ (Implication f1 f2 _ range))) t symbs 
		= let varass = Variable_Assignment []
                      test1 = calculateFormula (sign,f1) varass t symbs
		      test2 = calculateFormula (sign,f2) varass t symbs
		      res = not ((test1) && (not test2))
	          in if res then return True
                     else (warning False ("Implication does not hold: f1 is" ++
					  showDoc(simplify_sen CASL sign f1) "" ++ "f2 is " ++ 
					  showDoc(simplify_sen CASL sign f2) "")range)		    
 
modelCheckTest_ (sign, (SenAttr _ _ _ _ (Equivalence f1 f2 range))) t symbs 
		= let varass = Variable_Assignment []
		      test1 = calculateFormula (sign,f1) varass t symbs
		      test2 = calculateFormula (sign,f2) varass t symbs
		      res = test1 == test2	      
		 in  if res then return True
                     else (warning False ("Equivalence does not hold: f1 is" ++
					  showDoc(simplify_sen CASL sign f1) "" ++ "f2 is " ++ 
					  showDoc(simplify_sen CASL sign f2) "")range)	
		  

modelCheckTest_ (sign, (SenAttr _ _ _ _ (Negation f range))) t symbs 
		= let varass = Variable_Assignment []
		      res = calculateFormula (sign,f) varass t symbs
                  in if (not res) then return True
		                  else (warning False ("Negation does not hold:" 
						 ++ showDoc(simplify_sen CASL sign f) "") range)
modelCheckTest_ (sign, (SenAttr _ _ _ _ (Predication _ _ _))) _ _ 
		= error("not implemented Predication")
modelCheckTest_ (sign, (SenAttr _ _ _ _ (Existl_equation _ _ _))) _ _ 
		= error("not implemented Existl_equation")
modelCheckTest_ (sign, (SenAttr _ _ _ _ (True_atom _))) _ _ 
		= return True
modelCheckTest_ (sign, (SenAttr _ _ _ _ (False_atom range))) _ _ 
		= (warning False "False-atom cant be fulfilled!" range)
modelCheckTest_ (sign, (SenAttr _ _ _ _ (Definedness _ _))) _ _ 
		= error("not implemented Definedness")

modelCheckTest_ (sign, (SenAttr _ _ _ _ (Strong_equation t1 t2 range))) t symbs 
		= trace "Strong equation" $ 
		  let varass = Variable_Assignment []
		      res1 = calculateTerm (sign,t1) varass t symbs
		      res2 = calculateTerm (sign,t2) varass t symbs
		      equal = equalElements res1 res2
		  in if equal then return True
		     else (warning False 
				  ("Strong Equation does not hold term1:" 
				  ++ (showDoc t1 "") ++ 
				  "term2:"++(showDoc t2 "")) range) 
modelCheckTest_ (sign, (SenAttr _ _ _ _ (Mixfix_formula _))) _ _ 
		= error("not implemented Mixfix_formula")
modelCheckTest_ (sign, (SenAttr _ _ _ _ (Sort_gen_ax _ _))) _ _ 
		= error("not implemented Sort_gen_ax")
modelCheckTest_ (sign, (SenAttr _ _ _ _ (ExtFORMULA _))) _ _ 
		= error("not implemented ExtFormula" )  
modelCheckTest_ (sign, (SenAttr _ _ _ _ (Unparsed_formula _ _))) _ _ 
		= error("not implemented Unparsed_formula" )
modelCheckTest_ (sign, (SenAttr _ _ _ _ qf@(Quantification q decl f _))) t
		symbs 
		= let ass = generateVariableAssignments decl t
                  in
		  trace "modelcheckTest" $ calculateQuantification (sign,qf) 
		  ass t symbs
								     
modelCheckTest_ (sign, (SenAttr _ _ _ _ e)) _ _ 
		= error("not implemented" ++ show(e) )


calculateQuantification :: (Sign () (),FORMULA ()) -> [VARIABLE_ASSIGNMENT] -> 
			    Table -> [(OP_SYMB,String)]
			    -> Result Bool

calculateQuantification (sign, qf@(Quantification Universal decl f _)) 
			vardecls  t symbs 
			= trace ("calculateQuantUniv" ++ show(simplify_sen CASL sign qf)) $ calculateQuantificationUniversal (sign,qf) 
			  vardecls t symbs

calculateQuantification (sign, qf@(Quantification Existential decl f _)) 
			vardecls t symbs
			= calculateQuantificationExistential (sign,qf) 
			  vardecls t symbs 

calculateQuantification (sign, (Quantification Unique_existential _ _ _)) _ _ _ 
                        = error("not implemented Unique_existential ")


calculateQuantificationUniversal :: (Sign () (),(FORMULA ())) -> 
				    [VARIABLE_ASSIGNMENT] ->  Table -> 
				    [(OP_SYMB,String)] -> Result Bool

--calculateQuantificationUniversal _ []  _ _ 
--				 = (warning False 
--				 "Error: Empty VarAssignment" (Range []))

calculateQuantificationUniversal (sign,qf@(Quantification Universal decl f _)) 
				 ass t symbs 
				 = let Result d res = 
					   mapM (calculateQuantificationAtomar 
						(sign,qf) t symbs) ass
				   in Result d (liftM and res)



--				 = do calculateQuantificationUniversal 
--				       (sign,qf) [x] t symbs 
--				      calculateQuantificationUniversal 
--				       (sign,qf) xs t symbs

calculateQuantificationAtomar :: (Sign () (), (FORMULA ())) 
				          -> Table -> [(OP_SYMB,String)] 
					  -> VARIABLE_ASSIGNMENT
					  -> Result Bool   
					 
calculateQuantificationAtomar  (sign,qf@(Quantification _ 
						  decl f _))t symbs ass
				  = let res = calculateFormula (sign,f) ass 
						       t symbs
                                    in if (res == True) then return True
				       else (warning False (" "++ show(ass)) 
					     nullRange)
				   
--					 "Quantifier not fulfilled:\n"
--					 ++ showDoc (simplify_sen 
--					 CASL sign qf) "" ++ "\n" ++ show
--				         x) (Range []))    


--calculateQuantificationUniversal _ _ _ _  = error("wrong call calcQuantUniv ")
calculateQuantificationExistential :: (Sign () (),(FORMULA ())) -> 
				      [VARIABLE_ASSIGNMENT] ->  Table -> 
				      [(OP_SYMB,String)] -> Result Bool

calculateQuantificationExistential (sign,qf@(Quantification Existential 
						  decl f _)) ass t symbs 
				  = let  Result d res = 
					   mapM (calculateQuantificationAtomar 
						(sign,qf) t symbs) ass
				     in if ((liftM or res) == (Just True)) 
					 then return True
				        else (warning False
					     "Existential not fulfilled" 
					     nullRange)


data VARIABLE_ASSIGNMENT = Variable_Assignment [(VAR,Baserel)]
			   deriving (Eq) 

instance Show VARIABLE_ASSIGNMENT where 
 show (Variable_Assignment assignList) = showAssignments assignList

showAssignments :: [(VAR,Baserel)] -> String

showAssignments [] = "[]"
showAssignments xs = "["++ concat (intersperse ", " (map showSingleAssignment xs))  ++"]"

showSingleAssignment :: (VAR,Baserel) -> String
showSingleAssignment (v, Baserel b) = show(v) ++ "->"++b 



calculateTerm :: (Sign () (),(TERM ())) -> VARIABLE_ASSIGNMENT -> Table ->
		 [(OP_SYMB,String)] -> [Baserel]

calculateTerm (sign,(Simple_id var)) ass _ _
	       = getBaseRelForVariable var ass
calculateTerm (sign,(Qual_var var _ _)) ass _ _ = 
               getBaseRelForVariable var ass
calculateTerm (sign,(Application opSymb terms _)) ass t symbs =
	      applyOperation (getIdentifierForSymb opSymb symbs) (sign,terms)
	      t ass symbs

calculateTerm (sign,(Sorted_term term _ _)) ass t symbs = calculateTerm (sign,term)
	      ass t symbs

calculateTerm (sign,(Cast _ _ _)) _ _ _ = error("not implemented Cast")

-- wenn formula = true -> term1 sonst term2
calculateTerm (sign,(Conditional t1 fo t2 _)) ass t symbs = 
              let res = calculateFormula (sign,fo) ass t symbs
              in if res then (calculateTerm (sign,t1) ass t symbs)
		 else calculateTerm (sign,t2) ass t symbs


calculateTerm _ _ _ _ = []

getIdentifierForSymb :: OP_SYMB -> [(OP_SYMB,String)] -> String

getIdentifierForSymb symb tuplelist = concat (map (getIdentifierForSymbAtomar symb) tuplelist)  

getIdentifierForSymbAtomar :: OP_SYMB -> (OP_SYMB,String) -> String

getIdentifierForSymbAtomar symb (symb2,s) | symb == symb2 = s
                                          | otherwise = ""							    

--getIdentifierForSymb _ [] = ""
--getIdentifierForSymb symb [(symb2,s )] | symb == symb2 = s
				       | otherwise = ""
--getIdentifierForSymb symb (x:xs)   | (getIdentifierForSymb symb [x]) == "" 
--				     = (getIdentifierForSymb symb xs)
--				   | otherwise = (getIdentifierForSymb symb [x])
				       

applyOperation :: String -> (Sign () (),[(TERM ())]) -> Table 
		  -> VARIABLE_ASSIGNMENT -> [(OP_SYMB,String)]-> [Baserel]


applyOperation "RA_zero" (sign,[]) _ _ _ = []
applyOperation "RA_one" _ (Table (Table_Attrs _ _ baserels)
	      _ _ _ _) _ _ = baserels
applyOperation "RA_intersection" (sign,terms) table ass symbs = intersect 
	      (calculateTerm (sign,(head terms)) ass table symbs)
	      (calculateTerm (sign,(head (tail terms))) ass table symbs)  
applyOperation "RA_composition" (sign,terms) (Table attrs 
	      (Compositiontable cmpentries) convtbl refltbl models) 
	      ass symbs = calculateComposition cmpentries
	      (calculateTerm (sign,(head terms)) ass (Table attrs
	      (Compositiontable cmpentries) convtbl refltbl models) symbs)
	      (calculateTerm (sign,(head (tail terms))) ass (Table attrs 
	      (Compositiontable cmpentries) convtbl refltbl models) symbs)
applyOperation "RA_union" (sign,terms) table ass symbs = union 
	      (calculateTerm (sign,(head terms)) ass table symbs)
	      (calculateTerm (sign,(head(tail terms))) ass table symbs)
applyOperation "RA_complement" (sign,terms) (Table (Table_Attrs name id_
	       baserels) comptbl convtbl refltbl models) ass symbs = 
	       complement
	       (calculateTerm (sign,(head terms)) ass (Table (Table_Attrs
	       name id_ baserels) comptbl convtbl refltbl models)
	       symbs) baserels
applyOperation "RA_identity" _ (Table (Table_Attrs _ id_ _)
	       _ _ _ _) _ _ = [id_] 
applyOperation "RA_converse" (sign,terms) (Table attrs cmptable cnvtable
	       refltbl models)ass symbs = calculateConverse cnvtable 
	       (calculateTerm
	       (sign,(head terms)) ass (Table attrs cmptable cnvtable refltbl models)
	       symbs) 

applyOperation "RA_shortcut" (sign,terms) (Table attrs comptbl 
		(Conversetable_Ternary inv shortc hom) refltbl
		models) ass symbs = calculateConverseTernary shortc
		(calculateTerm (sign,(head terms)) ass (Table attrs comptbl 
		(Conversetable_Ternary inv shortc hom) refltbl
		models) symbs) 
applyOperation "RA_inverse" (sign,terms) (Table attrs comptbl 
		(Conversetable_Ternary inv shortc hom) refltbl
		models) ass symbs = calculateConverseTernary inv
		(calculateTerm (sign,(head terms)) ass (Table attrs comptbl 
		(Conversetable_Ternary inv shortc hom) refltbl
		models) symbs)  

applyOperation "RA_homing" (sign,terms) (Table attrs comptbl 
		(Conversetable_Ternary inv shortc hom) refltbl
		models) ass symbs = calculateConverseTernary hom
		(calculateTerm (sign,(head terms)) ass (Table attrs comptbl 
		(Conversetable_Ternary inv shortc hom) refltbl
		models) symbs) 
applyOperation _ _ _ _ _ = []


complement :: [Baserel] -> [Baserel] -> [Baserel]
complement rels baserles = baserles \\ rels

calculateComposition :: [Cmptabentry] -> [Baserel] -> [Baserel] ->
			[Baserel]

calculateComposition entries rels1 rels2 = foldr1 (++) (map (calculateComposition_ rels1 rels2) entries) 

--calculateComposition [] _ _ = []
--calculateComposition [x] rels1 rels2 = calculateComposition_ x rels1 rels2
--calculateComposition (x:xs) rels1 rels2 = calculateComposition_ x
--		     rels1 rels2 ++ calculateComposition xs rels1 rels2

calculateComposition_ :: [Baserel] -> [Baserel] -> Cmptabentry -> [Baserel]

calculateComposition_ rels1 rels2 (Cmptabentry (Cmptabentry_Attrs rel1 rel2) 
				   baserels)
		      | (rel1 `elem` rels1 ) && (rel2 `elem` rels2 ) =
		      baserels
		      | otherwise = []

calculateConverse:: Conversetable -> [Baserel] -> [Baserel]

calculateConverse (Conversetable_Ternary _ _ _) _ = [] 
calculateConverse (Conversetable centries) rels = foldr1 (++)(map 
						  (calculateConverseAtomar 
						  rels) centries)  

--calculateConverse (Conversetable []) _ = [] 
--calculateConverse (Conversetable [(Contabentry rel1 rel2)]) rels 
--		  | rel1 `elem` rels = [rel2]
--		  | otherwise = []
--calculateConverse (Conversetable (x:xs)) rels = (calculateConverse 
--		  (Conversetable [x]) rels) ++ (calculateConverse
--		  (Conversetable xs) rels)


calculateConverseAtomar :: [Baserel] -> Contabentry -> [Baserel] 
calculateConverseAtomar rels (Contabentry rel1 rel2)  | rel1 `elem` rels 
							  = [rel2]
						      | otherwise = []

calculateConverseTernary :: [Contabentry_Ternary] -> [Baserel] ->
			    [Baserel]
calculateConverseTernary entries rels = foldl1 (++) (map (calculateConverseTernaryAtomar rels) entries  )

calculateConverseTernaryAtomar ::  [Baserel] -> Contabentry_Ternary -> [Baserel]
calculateConverseTernaryAtomar rels2 (Contabentry_Ternary rel1 rels1)  
			  | rel1 `elem` rels2 = rels1
			  | otherwise = []
--calculateConverseTernary (x:xs) rels = calculateConverseTernary [x]
--				       rels ++
--				       calculateConverseTernary xs rels
  

getBaseRelForVariable :: VAR -> VARIABLE_ASSIGNMENT ->[Baserel]

getBaseRelForVariable var (Variable_Assignment tuples) = 
			  foldl1 (++) (map (getBaseRelForVariableAtomar var) 
				       tuples) 

getBaseRelForVariableAtomar :: VAR -> (VAR,Baserel) -> [Baserel]
getBaseRelForVariableAtomar v (var,baserel) 
			 | v == var = [baserel]
			 | otherwise = []  

--getBaseRelsForVariable v (Variable_Assignment (x:xs)) = 
--		       getBaseRelsForVariable v (Variable_Assignment [x]) ++
--		       getBaseRelsForVariable v (Variable_Assignment xs)


calculateFormula ::  (Sign () (),(FORMULA ())) -> VARIABLE_ASSIGNMENT -> Table -> 
		    [(OP_SYMB,String)] -> Bool

calculateFormula (sign,qf@(Quantification q vardecls f _)) varass t symbs = 
		 let (Result _ res) = (calculateQuantification (sign,qf) 
				       (appendVariableAssignments
				       [varass] vardecls t)  t symbs)
		 in 
		  (res == Just True) 
calculateFormula (sign,(Conjunction formulas _)) varass t symbs = 
		 and [calculateFormula (sign,x) varass t 
		     symbs | x<-formulas]
	        
calculateFormula (sign,(Disjunction formulas _)) varass t symbs = 
		 or [calculateFormula (sign,x) varass t 
		    symbs | x<-formulas]
calculateFormula (sign,(Implication f1 f2 _ _)) varass t symbs =
		 let test1 = calculateFormula (sign,f1) varass t symbs
		     test2 = calculateFormula (sign,f2) varass t symbs
		 in 
		  not ((test1) && (not test2)) 
		 
calculateFormula (sign,(Equivalence f1 f2 _)) varass t symbs =
		 let test1 = calculateFormula (sign,f1) varass t symbs
		     test2 = calculateFormula (sign,f2) varass t symbs
		 in
		  test1 == test2

calculateFormula (sign,(Negation f _)) varass t symbs = 
		 not (calculateFormula (sign,f) varass t symbs)
calculateFormula (sign,(True_atom _)) _ _ _ = True 
		 
calculateFormula (sign,(False_atom _)) _ _ _ = False
		
calculateFormula (sign,(Predication _ _ _)) _ _ _ = 
		 error "not implemented predication" 
		 
calculateFormula (sign,(Definedness _ _)) _ _ _ = 
		 error "not implemented definedness"
calculateFormula (sign,(Existl_equation _ _ _)) _ _ _ = 
		 error "not implemented existl"
calculateFormula (sign,(Strong_equation term1 term2 _)) varass t symbs =
		 let t1 = calculateTerm (sign,term1) varass t symbs
		     t2 = calculateTerm (sign,term2) varass t symbs
		 in if(equalElements t1 t2) then True
		    else False
   
		 
calculateFormula (sign,(Membership _ _ _)) _ _ _ = 
		 error "not implemented Membership"
calculateFormula (sign,(Unparsed_formula _ _)) _ _ _ = 
		 error "not implemented unparsed"
calculateFormula (sign,(Mixfix_formula _)) _ _ _ = 
		 error "not implemented mixfix"
calculateFormula _ _ _ _ = error "not implemented" 

--subsumes :: [Baserel] -> [Baserel] -> Bool

--subsumes a b | length a < length b = False
--            | otherwise = and (map (subsumesAtomar a) b)

--subsumesAtomar :: [Baserel] -> Baserel -> Bool
--subsumesAtomar rels rel = rel `elem` rels

equalElements :: [Baserel] -> [Baserel] -> Bool

equalElements a b = (Set.fromList a == Set.fromList b)

--subsumes _ [] = True
--subsumes [] _ = False
--subsumes (x:xs) [y] = x==y || (subsumes xs [y])
--subsumes x (y:ys) = (subsumes x [y]) && (subsumes x ys)   

generateVariableAssignments :: [VAR_DECL] -> Table -> [VARIABLE_ASSIGNMENT]

generateVariableAssignments vardecls t = trace "appendAssignments" $ map 
					 Variable_Assignment 
					 (gVA_ (getVars vardecls) 
					 (getBaseRelations t))

gVA_:: [VAR] -> [Baserel] -> [[(VAR,Baserel)]]

gVA_ [] baserels = [[]]
--gVA_ [v] baserels = map (\b -> [(v,b)]) baserels
gVA_ (v:vs) baserels = let rs = gVA_ vs baserels
			   fs = map (\b -> [(v,b)]) baserels
		       in [f ++ r | f<-fs, r<-rs]	
							


--generateVariableAssignments_ vars br = map Variable_Assignment
--				      (appendAssignments [] vars br)  



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

appendAssignments_ [] var baserels = appendAssignmentSingle var baserels []
appendAssignments_ list var baserels = foldl1 (++)(map (appendAssignmentSingle 
						       var baserels) list) 
--appendAssignments_ [x] var baserels = appendAssignmentSingle x var baserels 
--appendAssignments_ [] var baserels = appendAssignmentSingle [] var baserels
--appendAssignments_ (x:xs) var baserels = appendAssignmentSingle x var
--					 baserels ++ 
--					 appendAssignments_
--					 xs var baserels


appendAssignmentSingle:: VAR -> [Baserel] -> [(VAR,Baserel)] ->
			 [[(VAR,Baserel)]]
appendAssignmentSingle _ [] _ = [] 
appendAssignmentSingle var rels assignment = map (appendAssignmentSingle_ assignment var)
					     rels

appendAssignmentSingle_ :: [(VAR,Baserel)] -> VAR -> Baserel ->[(VAR,Baserel)]
appendAssignmentSingle_ acc var rel  = (var,rel):acc


getVars:: [VAR_DECL] -> [VAR]

getVars decls = (foldl1 (++) (map getVarsAtomic decls))

getVarsAtomic (Var_decl vars _ _) = vars
--getVars (x:xs) = (getVars [x]) ++ (getVars xs) 

getBaseRelations:: Table -> [Baserel]
getBaseRelations (Table (Table_Attrs _ _ br) _ _ _ _) = br

appendVariableAssignments :: [VARIABLE_ASSIGNMENT] -> [VAR_DECL] -> Table -> [VARIABLE_ASSIGNMENT]
appendVariableAssignments vars decls t = vars ++ (generateVariableAssignments decls t)
 
