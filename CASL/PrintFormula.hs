module PrintFormula where

import AS_Basic_CASL
import AS_Annotation
import Keywords
import Pretty
import PrettyPrint

instance PrettyPrint BASIC_SPEC where
    printText0 (Basic_spec l) = vcat (map printText0 l) 

dotT = space $$ (text middleDotS <> space)
semiT l = cat(punctuate semi (map printText0 l) )

instance PrettyPrint BASIC_ITEMS where
    printText0 (Sig_items s) = printText0 s
    printText0 (Free_datatype l _) = text freeS <+> text typeS
				 <+> vcat(map (\x -> printText0 x <> semi) l)
    printText0(Sort_gen l _) = text generatedS <+> vcat (map printText0 l)
    printText0(Var_items l _) = text varS 
				<+> semiT l
    printText0(Local_var_axioms l f _) = text forallS 
				 <+> semiT l
				 <+> dotT
				 <+> hcat(punctuate dotT (map printText0 f))
    printText0(Axiom_items f _) = dotT <> hcat(punctuate dotT (map printText0 f))

instance PrettyPrint SIG_ITEMS where
    printText0(Sort_items l _) =  text sortS <+> semiT l 
    printText0(Op_items l _) =  text opS <+> semiT l 
    printText0(Pred_items l _) =  text predS <+> semiT l 
    printText0(Datatype_items l) = text typeS <+> semiT l 

commaT l = cat(punctuate comma (map printText0 l))
equalT = space <> text equalS <> space

instance PrettyPrint SORT_ITEM where
    printText0(Sort_decl l _) = commaT l
    printText0(Subsort_decl l t _) = commaT l <+> text lessS 
			       <+> printText0 t
    printText0(Subsort_defn s v t f _) = printText0 s 
			       <+> text equalS 
			       <+> braces(printText0 s 
					  <+> colon
					  <+> printText0 t
					  <+> text middleDotS
					  <+> printText0 f)
    printText0(Iso_decl l _) = hcat(punctuate equalT (map printText0 l))

instance PrettyPrint OP_ITEM where
    printText0(Op_decl l t a _) = commaT l 
				  <+> colon
				  <+> printText0 t
				  <+> commaT a
    printText0(Op_defn n h t _) = printText0 n 
				  <+> printText0 h
                                  <+> text equalS
				  <+> printText0 t

timesT = space <> text timesS <> space 
crossT l = hcat(punctuate timesT (map printText0 l))

instance PrettyPrint OP_TYPE where
    printText0(Total_op_type l s _) = (if null l then empty else crossT l 
				       <+> text funS)
				      <+> printText0 s
    printText0(Partial_op_type l s _) = (if null l then text quMark 
					 else crossT l 
					 <+> text (funS ++ quMark))
					<+> printText0 s

instance PrettyPrint OP_HEAD where
    printText0(Total_op_head l s _) = parens(semiT l)
			     <+> colon
			     <+> printText0 s
    printText0(Partial_op_head l s _) = parens(semiT l)
			     <+> text (colonS ++ quMark)
			     <+> printText0 s

instance PrettyPrint ARG_DECL where
    printText0(Arg_decl l s _) = commaT l 
			      <+> colon
			      <+> printText0 s

instance PrettyPrint OP_ATTR where
    printText0(Assoc_op_attr) = text assocS
    printText0(Common_op_attr) = text commS 
    printText0(Idem_op_attr) = text idemS
    printText0(Unit_op_attr t) = text unitS <+> printText0 t

instance PrettyPrint PRED_ITEM where
    printText0(Pred_decl l t _) = commaT l 
				  <+> colon
				  <+> printText0 t
    printText0(Pred_defn n h f _) = printText0 n 
				  <+> printText0 h
                                  <+> text equivS
				  <+> printText0 f

instance PrettyPrint PRED_TYPE where
    printText0(Pred_type [] _) = parens (empty)
    printText0(Pred_type l _) = crossT l

instance PrettyPrint PRED_HEAD where
    printText0(Pred_head l _) = parens(semiT l)

barT = space <> text barS <> space

instance PrettyPrint DATATYPE_DECL where
    printText0(Datatype_decl s a _) = printText0 s 
				   <+> text defnS
				   <+> vcat(punctuate barT (map printText0 a))

instance PrettyPrint ALTERNATIVE where
    printText0(Total_construct n l _) = printText0 n 
				 <> parens(semiT l)
    printText0(Partial_construct n l _) = printText0 n 
				 <> parens(semiT l)
				 <> text quMark
    printText0(Subsorts l _) = text sortS <+> commaT l 

instance PrettyPrint COMPONENTS where
    printText0(Total_select l s _) = commaT l 
				<+> colon 
				<+> printText0 s 
    printText0(Partial_select l s _) = commaT l 
				<+> text (colonS ++ quMark) 
				<+> printText0 s 
    printText0(Sort s) = printText0 s 	  

instance PrettyPrint VAR_DECL where
    printText0(Var_decl l s _) = commaT l 
				<+> colon 
				<+> printText0 s 

instance PrettyPrint FORMULA where
    printText0(Quantification q l f _) = printText0 q
			     <+> semiT l
			     <+> text middleDotS
			     <+> printText0 f
    printText0(Conjunction l _) = parens(
		 cat(punctuate (space <> text lAnd <> space) (map printText0 l)))
    printText0(Disjunction  l _) = parens(
		 cat(punctuate (space <> text lOr <> space) (map printText0 l)))
    printText0(Implication f g _) = parens(printText0 f
			     <+> text implS
			     <+> printText0 g)
    printText0(Equivalence  f g _) = parens(printText0 f
			     <+> text equivS
			     <+> printText0 g)
    printText0(Negation f _) = text negS <+> printText0 f
    printText0(True_atom _) = text trueS
    printText0(False_atom _) = text falseS
    printText0(Predication p l _) = printText0 p <> 
				    (if null l then empty else parens(commaT l))
    printText0(Definedness f _) = text defS <+> printText0 f
    printText0(Existl_equation f g _) = printText0 f
			     <+> text exEqual
			     <+> printText0 g
    printText0(Strong_equation f g _) = printText0 f
			     <+> text equalS
			     <+> printText0 g 
    printText0(Membership f g _) = printText0 f
			     <+> text inS
			     <+> printText0 g
    printText0(Mixfix_formula t) = printText0 t
    printText0(Unparsed_formula s _) = text s 

instance PrettyPrint QUANTIFIER where
    printText0 (Universal) = text forallS
    printText0 (Existential) = text existsS
    printText0 (Unique_existential) = text (existsS ++ exMark)

instance PrettyPrint PRED_SYMB where
    printText0 (Pred_name n) = printText0 n
    printText0(Qual_pred_name n t _) = parens(text predS
					      <+> printText0 n
					      <+> colon
					      <+> printText0 t)
				       
instance PrettyPrint TERM where
    printText0(Simple_id i) = printText0 i
    printText0(Qual_var n t _) = parens(text varS
					<+> printText0 n
					<+> colon -- or :?
					<+> printText0 t)
    printText0(Application o l _) = printText0 o <> 
				    (if null l then empty else parens(commaT l))
    printText0(Sorted_term t s _) = printText0 t
			  <+> colon
			  <+> printText0 s
    printText0(Cast  t s _) = printText0 t
			  <+> text asS
			  <+> printText0 s
    printText0(Conditional u f v _) = parens(printText0 u
			  <+> text whenS
			  <+> printText0 f
			  <+> text elseS
			  <+> printText0 v)
    printText0(Unparsed_term s _) = text s
    printText0(Mixfix_term l) = cat(punctuate space (map printText0 l))
    printText0(Mixfix_token t) = printText0 t
    printText0(Mixfix_sorted_term s _) = colon
			  <+> printText0 s
    printText0(Mixfix_cast s _) = text asS
			  <+> printText0 s
    printText0(Mixfix_parenthesized l _) = parens(commaT l)
    printText0(Mixfix_bracketed l _) = brackets(commaT l)
    printText0(Mixfix_braced l _) = braces(commaT l)


isPartialConst(Partial_op_type [] _ _) = True
isPartialConst(_) = False

instance PrettyPrint OP_SYMB where
    printText0(Op_name o) = printText0 o
    printText0(Qual_op_name o t _) = parens(text opS
					    <+> printText0 o
					    <+> (colon <> 
						 (if isPartialConst t 
						  then empty 
						  else space) 
						 <> printText0 t))

