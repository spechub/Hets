
{- HetCATS/CASL/Print_AS_Basic.hs
   $Id$
   Authors: Christian Maeder
            Klaus Lüttich
   Year:    2002
   
   printing AS_BASIC data types

   todo:
     - improving printing of applications and predications
       consider string-, number-, list- and floating-annotations
       and also prec-, lassoc- and rassoc-annotations
-}

module CASL.Print_AS_Basic where

-- debugging
import Data.List (mapAccumL)
import Data.Char (isDigit)

import Common.Id
import CASL.AS_Basic_CASL
import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.GlobalAnnotationsFunctions
import CASL.LiteralFuns

import Common.Print_AS_Annotation

import Common.Keywords
import Common.Lib.Pretty
import Common.PrettyPrint
import Common.PPUtils

instance PrettyPrint BASIC_SPEC where
    printText0 ga (Basic_spec l) = 
	if null l then braces empty else vcat (map (printText0 ga) l) 
	     where _just_avoid_unused_import_warning = smallSpace_latex

    printLatex0 ga (Basic_spec l) = 
	if null l then braces_latex empty else vcat (map (printLatex0 ga) l) 

instance PrettyPrint BASIC_ITEMS where
    printText0 ga (Sig_items s) = printText0 ga s
    printText0 ga (Free_datatype l _) = 
	hang (ptext freeS <+> ptext typeS<>pluralS_doc l) 4 $ 
	     semiAnno_text ga l
    printText0 ga (Sort_gen l _) = 
	hang (ptext generatedS <+> condTypeS) 4 $ 
	     condBraces (vcat (map (printText0 ga) l))
	where condTypeS = 
		  if isOnlyDatatype then ptext typeS<>pluralS_doc l 
		  else empty
	      condBraces d = 
		  if isOnlyDatatype then 
		     case l of
		     [x] -> case x of
			    Annoted (Datatype_items l' _) _ lans _ -> 
				vcat (map (printText0 ga) lans) 
					 $$ semiAnno_text ga l'
			    _ -> error "wrong implementation of isOnlyDatatype"
                     _ -> error "wrong implementation of isOnlyDatatype"
		  else braces d
	      isOnlyDatatype = 
		  case l of
		  [x] -> case x of 
			 Annoted (Datatype_items _ _) _ _ _ -> True
			 _ -> False
		  _  -> False
    printText0 ga (Var_items l _) = 
	text varS<>pluralS_doc l <+> semiT_text ga l
    printText0 ga (Local_var_axioms l f p) = 
	text forallS <+> semiT_text ga l
		 $$ printText0 ga (Axiom_items f p)
    printText0 ga (Axiom_items f _) = 
	vcat $ map (printAnnotedFormula_Text0 ga) f

    printLatex0 ga (Sig_items s) = printLatex0 ga s 
    printLatex0 ga (Free_datatype l _) = 
	hang_latex (hc_sty_plain_keyword "free"
		    <~> setTab_latex
		    <> hc_sty_plain_keyword ("type"++ pluralS l)) 9 $
	           tabbed_nest_latex $ semiAnno_latex ga l
    printLatex0 ga (Sort_gen l _) = 
	hang_latex (hc_sty_plain_keyword generatedS 
		    <~> setTab_latex<> condTypeS) 9 $ 
	           tabbed_nest_latex $ condBraces  
				  (vcat (map (printLatex0 ga) l))
	where condTypeS = 
		  if isOnlyDatatype then 
		     hc_sty_plain_keyword (typeS++pluralS l) 
		  else empty
	      condBraces d = 
		  if isOnlyDatatype then 
		     case l of
		     [x] -> case x of
			    Annoted (Datatype_items l' _) _ lans _ -> 
				vcat (map (printLatex0 ga) lans) 
					 $$ semiAnno_latex ga l'
			    _ -> error "wrong implementation of isOnlyDatatype"
                     _ -> error "wrong implementation of isOnlyDatatype"
		  else braces_latex d
	      isOnlyDatatype = 
		  case l of
		  [x] -> case x of 
			 Annoted (Datatype_items _ _) _ _ _ -> True
			 _ -> False
		  _  -> False
    printLatex0 ga (Var_items l _) = 
	hc_sty_plain_keyword (varS++pluralS l) <\+> 
	semiT_latex ga l
    printLatex0 ga (Local_var_axioms l f p) = 
	hc_sty_axiom "\\forall" <\+> semiT_latex ga l
		 $$ printLatex0 ga (Axiom_items f p)
    printLatex0 ga (Axiom_items f _) = 
	vcat $ map (printAnnotedFormula_Latex0 ga) f

printAnnotedFormula_Text0 :: GlobalAnnos -> Annoted FORMULA -> Doc
printAnnotedFormula_Text0 ga (Annoted i _ las ras) =
	let i'   = char '.' <+> printText0 ga i
	    las' = if not $ null las then 
	               ptext "\n" <> printAnnotationList_Text0 ga las
		   else
		       empty
	    (la,rras) = case ras of
			[]     -> (empty,[])
			r@(l:xs)
			    | isLabel l -> (printText0 ga l,xs)
			    | otherwise -> (empty,r)
	    ras' = printAnnotationList_Text0 ga rras
        in las' $+$ (hang i' 0 la) $$ ras'

printAnnotedFormula_Latex0 :: GlobalAnnos -> Annoted FORMULA -> Doc
printAnnotedFormula_Latex0 ga (Annoted i _ las ras) =
	let i'   = hc_sty_axiom "\\bullet" <\+> printLatex0 ga i
	    las' = if not $ null las then 
	              sp_text 0 "\n" <> printAnnotationList_Latex0 ga las
	           else
		      empty
	    (la,rras) = case ras of
			[]     -> (empty,[])
			r@(l:xs)
			    | isLabel l -> (printLatex0 ga l,xs)
			    | otherwise -> (empty,r)
	    ras' = printAnnotationList_Latex0 ga rras
        in  las' $+$ (hang_latex i' 0 la) $$ ras'


instance PrettyPrint SIG_ITEMS where
    printText0 ga (Sort_items l _) =  
	text sortS<>pluralS_doc l <+> semiAnno_text ga l
    printText0 ga (Op_items l _) =  
	text opS<>pluralS_doc l <+> semiAnno_text ga l 
    printText0 ga (Pred_items l _) =  
	text predS<>pluralS_doc l <+> semiAnno_text ga l 
    printText0 ga (Datatype_items l _) = 
	text typeS<>pluralS_doc l <+> semiAnno_text ga l 

    printLatex0 ga (Sort_items l _) =  
	hc_sty_casl_keyword (sortS++pluralS l) <\+>
	set_tabbed_nest_latex (semiAnno_latex ga l)
    printLatex0 ga (Op_items l _) =  
	hc_sty_casl_keyword (opS++pluralS l)   <\+> 
	set_tabbed_nest_latex (semiAnno_latex ga l) 
    printLatex0 ga (Pred_items l _) =  
	hc_sty_casl_keyword (predS++pluralS l) <\+> 
	set_tabbed_nest_latex (semiAnno_latex ga l) 
    printLatex0 ga (Datatype_items l _) = 
	hc_sty_casl_keyword (typeS++pluralS l) <\+> 
	set_tabbed_nest_latex (semiAnno_latex ga l) 

instance PrettyPrint SORT_ITEM where
    printText0 ga (Sort_decl l _) = commaT_text ga l
    printText0 ga (Subsort_decl l t _) = 
	hang (commaT_text ga l) 4 $ text lessS <+> printText0 ga t
    printText0 ga (Subsort_defn s v t f _) = 
	-- TODO: lannos of f should printed after the equal sign 
	printText0 ga s <+> ptext equalS <+> 
	   braces (hang (printText0 ga v <+> colon <+> printText0 ga t) 
		         4 (ptext "." <+> printText0 ga f))
    printText0 ga (Iso_decl l _) = 
	fsep $ punctuate  (space <>text equalS) $ map (printText0 ga) l

    printLatex0 ga (Sort_decl l _) = commaT_latex ga l
    printLatex0 ga (Subsort_decl l t _) = 
	hang_latex (commaT_latex ga l) 8 $ 
		   hc_sty_axiom lessS <\+> printLatex0 ga t
    printLatex0 ga (Subsort_defn s v t f _) = 
	printLatex0 ga s <\+> equals_latex <\+> 
	   braces_latex (hang_latex (     printLatex0 ga v 
				     <\+> colon_latex 
				     <\+> printLatex0 ga t) 
		         8 (hc_sty_axiom "\\bullet" <\+> printLatex0 ga f))
    printLatex0 ga (Iso_decl l _) = 
	fsep_latex $ punctuate  (space_latex<>equals_latex) $ 
		   map (printLatex0 ga) l

instance PrettyPrint OP_ITEM where
    printText0 ga (Op_decl l t a _) = 
	hang (hang (commaT_text ga l) 
	            4 
	            (colon <> printText0 ga t <> condComma)) 
             4 $
	       if na then empty 
	       else commaT_text ga a
	where na = null a
	      condComma = if na then empty
			  else comma
    printText0 ga (Op_defn n h t _) = printText0 ga n 
				  <> printText0 ga h
                                  <+> text equalS
				  <+> printText0 ga t

    printLatex0 ga (Op_decl l t a _) = 
	{-cat [ cat [commaT_latex ga l
		  ,colon_latex <> printLatex0 ga t <> condComma] 
            , if na then empty 
	      else commaT_latex ga a
	    ]-}
        if na then ids_sig
	else setTabWithSpaces_latex 4 
		 <> 
		 (tab_hang_latex ids_sig
		                 4 $ commaT_latex ga a)
	where ids_sig = setTabWithSpaces_latex 6 
			<> tab_hang_latex (commaT_latex ga l) 
	                                  6 
	                                  (if na then sig 
					   else sig <> comma_latex)
	      sig = colon_latex <> printLatex0 ga t 
	      na = null a

    printLatex0 ga (Op_defn n h t _) = printLatex0 ga n 
				  <> printLatex0 ga h
                                  <\+> equals_latex
				  <\+> printLatex0 ga t

instance PrettyPrint OP_TYPE where
    printText0 ga (Total_op_type l s _) = (if null l then empty
					   else space 
					        <> crossT_text ga l 
				                <+> text funS)
				           <> space <> printText0 ga s
    printText0 ga (Partial_op_type l s _) = (if null l then text quMark 
					     else space 
                                                  <> crossT_text ga l 
					          <+> text (funS ++ quMark))
					    <+> printText0 ga s

    printLatex0 ga (Total_op_type l s _) = 
	(if null l then empty
	 else space_latex <>
	      set_tabbed_nest_latex (crossT_latex ga l
				     <\+> hc_sty_axiom "\\rightarrow"))
				     <~> printLatex0 ga s
    printLatex0 ga (Partial_op_type l s _) = 
	(if null l then hc_sty_axiom quMark 
	 else space_latex
              <> crossT_latex ga l 
	      <\+> hc_sty_axiom ("\\rightarrow" ++ quMark))
	<~> printLatex0 ga s

instance PrettyPrint OP_HEAD where
    printText0 ga (Total_op_head l s _) = 
	(if null l then empty 
	 else parens(semiT_text ga l))
	<> colon
	<+> printText0 ga s
    printText0 ga (Partial_op_head l s _) = 
	(if null l then empty 
	 else parens(semiT_text ga l))
	<> text (colonS ++ quMark)
        <+> printText0 ga s

    printLatex0 ga (Total_op_head l s _) = 
	(if null l then empty 
	 else parens_latex (semiT_latex ga l))
	<> colon_latex
	<\+> printLatex0 ga s
    printLatex0 ga (Partial_op_head l s _) = 
	(if null l then empty 
	 else parens_latex(semiT_latex ga l))
	<> colon_latex <> hc_sty_axiom quMark
        <\+> printLatex0 ga s

instance PrettyPrint ARG_DECL where
    printText0 ga (Arg_decl l s _) = commaT_text ga l 
			      <+> colon
			      <> printText0 ga s

    printLatex0 ga (Arg_decl l s _) = commaT_latex ga l 
			      <\+> colon_latex
			      <> printLatex0 ga s

instance PrettyPrint OP_ATTR where
    printText0 _ (Assoc_op_attr)   = text assocS
    printText0 _ (Comm_op_attr)    = text commS 
    printText0 _ (Idem_op_attr)    = text idemS
    printText0 ga (Unit_op_attr t) = text unitS <+> printText0 ga t

    printLatex0 _ (Assoc_op_attr)   = hc_sty_id assocS
    printLatex0 _ (Comm_op_attr)    = hc_sty_id commS 
    printLatex0 _ (Idem_op_attr)    = hc_sty_id idemS
    printLatex0 ga (Unit_op_attr t) = hc_sty_id unitS <\+> printLatex0 ga t

instance PrettyPrint PRED_ITEM where
    printText0 ga (Pred_decl l t _) = commaT_text ga l 
				  <+> colon <+> printText0 ga t
    printText0 ga (Pred_defn n h f _) = printText0 ga n 
				        <> printText0 ga h
                                        <+> text equivS
				        <+> printText0 ga f

    printLatex0 ga (Pred_decl l t _) = commaT_latex ga l 
				  <\+> colon_latex <\+> printLatex0 ga t
    printLatex0 ga (Pred_defn n h f _) = printLatex0 ga n 
				        <> printLatex0 ga h
                                        <\+> hc_sty_axiom "\\Leftrightarrow"
				        <\+> printLatex0 ga f

instance PrettyPrint PRED_TYPE where
    printText0 _ (Pred_type [] _) = parens empty
    printText0 ga (Pred_type l _) = crossT_text ga l

    printLatex0 _ (Pred_type [] _) = parens_latex empty
    printLatex0 ga (Pred_type l _) = crossT_latex ga l

instance PrettyPrint PRED_HEAD where
    printText0 ga (Pred_head l _) = parens (semiT_text ga l)

    printLatex0 ga (Pred_head l _) = 
	parens_latex (semiT_latex ga l)

instance PrettyPrint DATATYPE_DECL where
    printText0 ga (Datatype_decl s a _) = 
	printText0 ga s <+> 
	sep ((hang (text defnS) 4 (printText0 ga $ head a)):
	     (map (\x -> nest 2 $ ptext barS <+> nest 2 (printText0 ga x)) $ 
		  tail a))

    printLatex0 ga (Datatype_decl s a _) = 
	printLatex0 ga s <\+> 
	sep_latex 
	   ((hang_latex (hc_sty_axiom defnS) 8 (printLatex0 ga $ head a)):
	    (map (\x -> nest_latex 4 $ casl_normal_latex "\\textbar" 
			    <\+> nest_latex 4 (printLatex0 ga x)) $ 
	         tail a))

instance PrettyPrint ALTERNATIVE where
    printText0 ga (Total_construct n l _) = printText0 ga n 
				 <> if null l then empty 
				    else parens(semiT_text ga l)
    printText0 ga (Partial_construct n l _) = printText0 ga n 
				 <> parens(semiT_text ga l)
				 <> text quMark
    printText0 ga (Subsorts l _) = text sortS <+> commaT_text ga l 

    printLatex0 ga (Total_construct n l _) = 
	printLatex0 ga n <> if null l then empty 
		            else parens_latex (semiT_latex ga l)
    printLatex0 ga (Partial_construct n l _) = printLatex0 ga n 
				 <> parens_latex (semiT_latex ga l)
				 <> hc_sty_axiom quMark 
    printLatex0 ga (Subsorts l _) = 
	hc_sty_plain_keyword sortS <\+> commaT_latex ga l 

instance PrettyPrint COMPONENTS where
    printText0 ga (Total_select l s _) = commaT_text ga l 
				<> colon 
				<> printText0 ga s 
    printText0 ga (Partial_select l s _) = commaT_text ga l 
				<> text (colonS ++ quMark) 
				<> printText0 ga s 
    printText0 ga (Sort s) = printText0 ga s 	  

    printLatex0 ga (Total_select l s _) = 
	commaT_latex ga l <> colon_latex <> printLatex0 ga s 
    printLatex0 ga (Partial_select l s _) = 
	commaT_latex ga l 
			 <> colon_latex <> hc_sty_axiom quMark 
			 <> printLatex0 ga s 
    printLatex0 ga (Sort s) = printLatex0 ga s 	  

instance PrettyPrint VAR_DECL where
    printText0 ga (Var_decl l s _) = commaT_text ga l 
				<> colon 
				<> printText0 ga s 

    printLatex0 ga (Var_decl l s _) = commaT_latex ga l 
				<> colon_latex 
				<> printLatex0 ga s 

instance PrettyPrint FORMULA where
    printText0 ga (Quantification q l f _) = 
	hang (printText0 ga q <+> semiT_text ga l) 4 $ 
	     char '.' <+> printText0 ga f
    printText0 ga (Conjunction l _) = 
	sep $ prepPunctuate (ptext lAnd <> space) $ 
	    map (condParensXjunction printText0 parens ga) l
    printText0 ga (Disjunction  l _) = 
	sep $ prepPunctuate (ptext lOr <> space) $ 
	    map (condParensXjunction printText0 parens ga) l
    printText0 ga i@(Implication f g _) = 
	hang (condParensImplEquiv printText0 parens ga i f 
	      <+> ptext implS) 4 $ 
	     condParensImplEquiv printText0 parens ga i g
    printText0 ga e@(Equivalence  f g _) = 
	hang (condParensImplEquiv printText0 parens ga e f 
	      <+> ptext equivS) 4 $
	     condParensImplEquiv printText0 parens ga e g
    printText0 ga (Negation f _) = ptext "not" <+> printText0 ga f
    printText0 _ (True_atom _)  = ptext trueS
    printText0 _ (False_atom _) = ptext falseS
    printText0 ga (Predication p l _) = 
	let (p_id,isQual) = 
		case p of
		       Pred_name i          -> (i,False)
		       Qual_pred_name i _ _ -> (i,True)
	    p' = printText0 ga p
	in if isQual then 
	     print_prefix_appl_text ga p' l  
	   else condPrint_Mixfix_text ga p_id l
    printText0 ga (Definedness f _) = text defS <+> printText0 ga f
    printText0 ga (Existl_equation f g _) = 
	hang (printText0 ga f <+> ptext exEqual) 4 $ printText0 ga g
    printText0 ga (Strong_equation f g _) = 
	hang (printText0 ga f <+> ptext equalS) 4 $ printText0 ga g 
    printText0 ga (Membership f g _) = 
	printText0 ga f <+> ptext inS <+> printText0 ga g
    printText0 ga (Mixfix_formula t) = printText0 ga t
    printText0 _ (Unparsed_formula s _) = text s 

    printLatex0 ga (Quantification q l f _) = 
	hang_latex (printLatex0 ga q <\+> semiT_latex ga l) 8 $ 
	     hc_sty_axiom "\\bullet" <\+> printLatex0 ga f
    printLatex0 ga (Conjunction l _) = 
	sep_latex $ prepPunctuate (hc_sty_axiom "\\wedge" <> space_latex) $ 
	    map (condParensXjunction printLatex0 parens_latex ga) l
    printLatex0 ga (Disjunction  l _) = 
	sep_latex $ prepPunctuate (hc_sty_axiom "\\vee" <> space_latex) $ 
	    map (condParensXjunction printLatex0 parens_latex ga) l 
    printLatex0 ga i@(Implication f g _) = 
	hang_latex (condParensImplEquiv printLatex0 parens_latex ga i f 
		    <\+> hc_sty_axiom "\\Rightarrow") 8 $ 
	     condParensImplEquiv printLatex0 parens_latex ga i g
    printLatex0 ga e@(Equivalence  f g _) = 
	hang_latex (condParensImplEquiv printLatex0 parens_latex ga e f 
		    <\+> hc_sty_axiom "\\Leftrightarrow") 8 $
	     condParensImplEquiv printLatex0 parens_latex ga e g
    printLatex0 ga (Negation f _) = hc_sty_axiom "\\neg" <\+> printLatex0 ga f
    printLatex0 _ (True_atom _)  = hc_sty_id trueS
    printLatex0 _ (False_atom _) = hc_sty_id falseS
    printLatex0 ga (Predication p l _) = 
	let (p_id,isQual) = 
		case p of
		       Pred_name i          -> (i,False)
		       Qual_pred_name i _ _ -> (i,True)
	    p' = printLatex0 ga p
	in if isQual then 
	     print_prefix_appl_latex ga p' l
	   else condPrint_Mixfix_latex ga p_id l
    printLatex0 ga (Definedness f _) = hc_sty_id defS <\+> printLatex0 ga f
    printLatex0 ga (Existl_equation f g _) = 
	hang_latex (printLatex0 ga f 
		    <\+> sp_text (axiom_width "=") 
		                 "\\Ax{\\stackrel{e}{=}}") 8 
		       $ printLatex0 ga g
    printLatex0 ga (Strong_equation f g _) = 
	hang_latex (printLatex0 ga f <\+> hc_sty_axiom "=") 8 
		       $ printLatex0 ga g 
    printLatex0 ga (Membership f g _) = 
	printLatex0 ga f <\+> hc_sty_axiom "\\in" <\+> printLatex0 ga g
    printLatex0 ga (Mixfix_formula t) = printLatex0 ga t
    printLatex0 _ (Unparsed_formula s _) = text s 

instance PrettyPrint QUANTIFIER where
    printText0 _ (Universal) = ptext forallS
    printText0 _ (Existential) = ptext existsS
    printText0 _ (Unique_existential) = ptext (existsS ++ exMark)

    printLatex0 _ (Universal) = hc_sty_axiom "\\forall"
    printLatex0 _ (Existential) = hc_sty_axiom "\\exists"
    printLatex0 _ (Unique_existential) = hc_sty_axiom "\\exists!"

instance PrettyPrint PRED_SYMB where
    printText0 ga (Pred_name n) = printText0 ga n
    printText0 ga (Qual_pred_name n t _) = 
	parens $ ptext predS <+> printText0 ga n <+> colon <+> printText0 ga t
				       
    printLatex0 ga (Pred_name n) = printLatex0 ga n
    printLatex0 ga (Qual_pred_name n t _) = 
	parens_latex $ hc_sty_id predS 
			 <\+> printLatex0 ga n 
			 <\+> colon_latex <\+> printLatex0 ga t

instance PrettyPrint TERM where
    printText0 ga (Simple_id i) = printText0 ga i
    printText0 ga (Qual_var n t _) = 
	parens $ text varS <+> printText0 ga n <+> colon <+> printText0 ga t
    printText0 ga (Application o l _) = 
	let (o_id,isQual) = 
		case o of
		       Op_name i          -> (i,False)
		       Qual_op_name i _ _ -> (i,True)
	    o' = printText0 ga o
	in if isQual then 
	     print_prefix_appl_text ga o' l
	   else 
	     if isLiteral ga o_id l then
	       {-trace ("a literal application: " 
		      ++ show (Application o l [])) $ -}
		     print_Literal_text ga o_id l
	     else
	       condPrint_Mixfix_text ga o_id l
    printText0 ga (Sorted_term t s _) = 
	printText0 ga t	<+> colon <+> printText0 ga s
    printText0 ga (Cast  t s _) = 
	printText0 ga t <+> text asS <+> printText0 ga s
    printText0 ga(Conditional u f v _) = 
	hang (printText0 ga u) 4 $ 
	     sep ((text whenS <+> printText0 ga f):
		     [text elseS <+> printText0 ga v])
    printText0 _ (Unparsed_term s _) = text s
    printText0 ga (Mixfix_qual_pred p) = printText0 ga p
    printText0 ga (Mixfix_term l) = 
	cat(punctuate space (map (printText0 ga) l))
    printText0 ga (Mixfix_token t) = printText0 ga t
    printText0 ga (Mixfix_sorted_term s _) = colon
					     <> printText0 ga s
    printText0 ga (Mixfix_cast s _) = text asS
				     <+> printText0 ga s
    printText0 ga (Mixfix_parenthesized l _) = parens (commaT_text ga l)
    printText0 ga (Mixfix_bracketed l _) =   brackets (commaT_text ga l)
    printText0 ga (Mixfix_braced l _) =        braces (commaT_text ga l)

    printLatex0 ga (Simple_id i) = printLatex0 ga i
    printLatex0 ga (Qual_var n t _) = -- HERE
	parens_latex $ hc_sty_id varS 
			 <\+> printLatex0 ga n 
			 <\+> colon_latex <\+> printLatex0 ga t
    printLatex0 ga (Application o l _) = 
	let (o_id,isQual) = 
		case o of
		       Op_name i          -> (i,False)
		       Qual_op_name i _ _ -> (i,True)
	    o' = printLatex0 ga o
	in if isQual then 
	     print_prefix_appl_latex ga o' l
	   else 
	     if isLiteral ga o_id l then
	       print_Literal_latex ga o_id l
	     else
	       condPrint_Mixfix_latex ga o_id l
    printLatex0 ga (Sorted_term t s _) = 
	printLatex0 ga t	<\+> colon_latex <\+> printLatex0 ga s
    printLatex0 ga (Cast  t s _) = 
	printLatex0 ga t <\+> hc_sty_id asS <\+> printLatex0 ga s
    printLatex0 ga(Conditional u f v _) = 
	hang_latex (printLatex0 ga u) 8 $ 
	     sep_latex ((hc_sty_id whenS <\+> printLatex0 ga f):
		     [hc_sty_id elseS <\+> printLatex0 ga v])
    printLatex0 _ (Unparsed_term s _) = text s
    printLatex0 ga (Mixfix_qual_pred p) = printLatex0 ga p
    printLatex0 ga (Mixfix_term l) = 
	cat(punctuate space (map (printLatex0 ga) l))
    printLatex0 ga (Mixfix_token t) = printLatex0 ga t
    printLatex0 ga (Mixfix_sorted_term s _) = colon
					     <> printLatex0 ga s
    printLatex0 ga (Mixfix_cast s _) = text asS
				     <\+> printLatex0 ga s
    printLatex0 ga (Mixfix_parenthesized l _) = 
	parens_latex (commaT_latex ga l)
    printLatex0 ga (Mixfix_bracketed l _) =   
	brackets_latex (commaT_latex ga l)
    printLatex0 ga (Mixfix_braced l _) =        
	braces_latex (commaT_latex ga l)

instance PrettyPrint OP_SYMB where
    printText0 ga (Op_name o) = printText0 ga o
    printText0 ga (Qual_op_name o t _) = parens(text opS
						<+> printText0 ga o
						<+> (colon
						     <> printText0 ga t))

    printLatex0 ga (Op_name o) = printLatex0 ga o
    printLatex0 ga (Qual_op_name o t _) = 
	parens_latex
	  (hc_sty_id opS
	   <\+> printLatex0 ga o <\+> colon_latex <> printLatex0 ga t)

instance PrettyPrint SYMB_ITEMS where
    printText0 ga (Symb_items k l _) = 
	printText0 ga k <> ptext (pluralS_symb_list k l) 
		        <+> commaT_text ga l

    printLatex0 ga (Symb_items k l _) = 
	print_kind_latex ga k l <\+> commaT_latex ga l
	

instance PrettyPrint SYMB_ITEMS_LIST where
    printText0 ga (Symb_items_list l _) = commaT_text ga l

    printLatex0 ga (Symb_items_list l _) = commaT_latex ga l

instance PrettyPrint SYMB_MAP_ITEMS where
    printText0 ga (Symb_map_items k l _) = 
	printText0 ga k <> ptext (pluralS_symb_list k l) 
		        <+> commaT_text ga l

    printLatex0 ga (Symb_map_items k l _) = 
	print_kind_latex ga k l <\+> commaT_latex ga l

instance PrettyPrint SYMB_MAP_ITEMS_LIST where 
    printText0 ga (Symb_map_items_list l _) = commaT_text ga l

    printLatex0 ga (Symb_map_items_list l _) = commaT_latex ga l

instance PrettyPrint SYMB_KIND where 
    printText0 _ Implicit   = empty
    printText0 _ Sorts_kind = ptext sortS
    printText0 _ Ops_kind   = ptext opS
    printText0 _ Preds_kind = ptext predS

    printLatex0 _ Implicit   = empty
    printLatex0 _ Sorts_kind = casl_keyword_latex sortS
    printLatex0 _ Ops_kind   = casl_keyword_latex opS
    printLatex0 _ Preds_kind = casl_keyword_latex predS

instance PrettyPrint SYMB where 
    printText0 ga (Symb_id i) = printText0 ga i
    printText0 ga (Qual_id i t _) = 
	printText0 ga i <+> colon <+> printText0 ga t

    printLatex0 ga (Symb_id i) = printLatex0 ga i
    printLatex0 ga (Qual_id i t _) = 
	printLatex0 ga i <\+> colon_latex <\+> printLatex0 ga t

instance PrettyPrint TYPE where 
    printText0 ga (O_type t) = printText0 ga t
    printText0 ga (P_type t) = printText0 ga t
    printText0 ga (A_type t) = printText0 ga t

    printLatex0 ga (O_type t) = printLatex0 ga t
    printLatex0 ga (P_type t) = printLatex0 ga t
    printLatex0 ga (A_type t) = printLatex0 ga t

instance PrettyPrint SYMB_OR_MAP where 
    printText0 ga (Symb s) = printText0 ga s
    printText0 ga (Symb_map s t _) = 
	printText0 ga s <+> text mapsTo <+> printText0 ga t

    printLatex0 ga (Symb s) = printLatex0 ga s
    printLatex0 ga (Symb_map s t _) = 
	printLatex0 ga s <\+> hc_sty_axiom "\\mapsto" <\+> printLatex0 ga t

---- helpers ----------------------------------------------------------------

pluralS_symb_list :: SYMB_KIND -> [a] -> String
pluralS_symb_list k l = case k of
		       Implicit -> ""
		       _        -> if length l > 1 
				   then "s" 
				   else ""

print_kind_latex :: GlobalAnnos -> SYMB_KIND -> [a] -> Doc
print_kind_latex ga k l = latex_macro "\\KW{"<>kw<>s<>latex_macro "}"
    where kw = printLatex0 ga k
	  s  = case pluralS_symb_list k l of
	       "" -> empty 
	       s' -> casl_keyword_latex s'

condPrint_Mixfix :: (forall a .PrettyPrint a => GlobalAnnos -> a -> Doc)
		 -> (Doc -> Doc)    -- ^ a function that surrounds 
				    -- the given Doc with appropiate 
				    -- parens
		 -> (Doc -> Doc -> Doc) -- ^ a beside with space 
					-- like <+> or <\+>
		 -> ([Doc] -> Doc)    -- ^ a list concat with space and 
				      -- fill the line policy  like
				      -- fsep or fsep_latex
		 -> (forall b . PrettyPrint b => 
		          GlobalAnnos -> [b] -> Doc)
		          -- ^ a function that prints a nice 
			  -- comma seperated list like commaT 
			  -- or commaT_latex
		 ->  GlobalAnnos -> Id -> [TERM] -> Doc
condPrint_Mixfix pf parens_fun
		 beside_fun fsep_fun commaT_fun 
		 ga i l =
    if isMixfix i then
       if length (filter isPlace tops) == length l then
	  print_mixfix_appl pf parens_fun 
			    beside_fun fsep_fun ga i l
       else 
          print_prefix_appl parens_fun commaT_fun ga o' l
    else print_prefix_appl parens_fun commaT_fun ga o' l
    where tops = case i of Id tp _ _ -> tp 
	  o' = pf ga i
{- TODO: consider string-, number-, list- and floating-annotations -}

condPrint_Mixfix_text :: GlobalAnnos -> Id -> [TERM] -> Doc
condPrint_Mixfix_text =
    condPrint_Mixfix printText0 parens 
		     (<+>) fsep (commaT_text)

condPrint_Mixfix_latex :: GlobalAnnos -> Id -> [TERM] -> Doc
condPrint_Mixfix_latex =
    condPrint_Mixfix printLatex0 parens_latex 
		     (<\+>) fsep_latex (commaT_latex)

-- printing consistent prefix application and predication
print_prefix_appl :: (Doc -> Doc)    -- ^ a function that surrounds 
				     -- the given Doc with appropiate 
				     -- parens
		  -> (forall b . PrettyPrint b => 
		          GlobalAnnos -> [b] -> Doc)
		          -- ^ a function that prints a nice 
			  -- comma seperated list like commaT 
			  -- or commaT_latex
		  -> GlobalAnnos -> Doc -> [TERM] -> Doc 
print_prefix_appl parens_fun commaT_fun ga po' l = po' <> 
			     (if null l then empty 
			      else parens_fun (commaT_fun ga l))

print_prefix_appl_text :: GlobalAnnos -> Doc -> [TERM] -> Doc
print_prefix_appl_text =
    print_prefix_appl parens (commaT_text)

print_prefix_appl_latex :: GlobalAnnos -> Doc -> [TERM] -> Doc
print_prefix_appl_latex = 
    print_prefix_appl parens_latex (commaT_latex)

print_Literal :: (forall a .PrettyPrint a => GlobalAnnos -> a -> Doc)
	      -> (Doc -> Doc)    -- ^ a function that surrounds 
				 -- the given Doc with appropiate 
				 -- parens
	      -> (Doc -> Doc -> Doc)    -- ^ a beside with space 
					-- like <+> or <\+>
	      -> ([Doc] -> Doc)    -- ^ a list concat with space and 
				   -- fill the line policy  like
				   -- fsep or fsep_latex
	      -> (forall b . PrettyPrint b => 
		          GlobalAnnos -> [b] -> Doc)
		          -- ^ a function that prints a nice 
			  -- comma seperated list like commaT 
			  -- or commaT_latex
	      -> Doc   -- ^ a document containing the dot for a Fraction
	      -> Doc   -- ^ a document containing the 'E' of a Floating
	      -> GlobalAnnos -> Id -> [TERM] -> Doc
print_Literal pf parens_fun 
	      beside_fun fsep_fun commaT_fun dot_doc e_doc
	      ga li ts 
    | isSignedNumber ga li ts = let [t_ts] = ts
				in pf ga li <> 
				       ((uncurry p_l) (splitAppl t_ts))
    | isNumber ga li ts = hcat $ map (pf ga) $ toksNumber li
    | isFrac   ga li ts = let [lt,rt] = ts
			      (lni,lnt) = splitAppl lt
			      (rni,rnt) = splitAppl rt
			      ln = p_l lni lnt
			      rn = p_l rni rnt
			  in ln <> dot_doc <> rn
    | isFloat  ga li ts = let [bas,ex] = ts
			      (bas_i,bas_t) = splitAppl bas
			      (ex_i,ex_t)   = splitAppl ex
			      bas_d = p_l bas_i bas_t
			      ex_d  = p_l ex_i ex_t
			  in bas_d <> e_doc <> ex_d
    | isList   ga li ts = let list_body = commaT_fun ga $ listElements li
			      (openL, closeL, comps) = getListBrackets $ 
						       listBrackets ga li
 			  in hcat(map (pf ga) openL) <+> list_body 
			     <+> hcat(map (pf ga) closeL)
			     <> pf ga (Id [] comps [])
    | isString ga li ts = ptext $ 
			  (\s -> let r = '"':(s ++ "\"") in seq r r) $ 
			  concatMap convCASLChar $ toksString li
    | otherwise = condPrint_Mixfix pf parens_fun 
		                   beside_fun fsep_fun commaT_fun 
				   ga li ts
    where p_l = print_Literal pf parens_fun
				 beside_fun fsep_fun
				 commaT_fun dot_doc e_doc ga

	  toksNumber i   = if tokIsDigit then
			     [tok]
			   else
			     map (termToTok "number") $
				 collectElements Nothing i ts
	     where tok = case i of
			 Id []     _ _ -> error "malformed Id!!!"
			 Id [tokk] [] _ -> tokk
			 Id (x:_) _ _ -> x 
		   tokIsDigit = (isDigit $ head $ tokStr $ tok) && null ts
	  toksString i   = case getLiteralType ga i of 
			   StringNull -> []
			   StringCons n -> map (termToTok "string") $ 
				   collectElements (Just n) i ts
			   _ -> error "toksString"
	  termToTok tokType x = case basicTerm x of
				Just tokk -> tokk
				Nothing   -> error ("malformed " ++ tokType)
	  listElements i = case getLiteralType ga i of
			   ListNull _ -> []
			   ListCons _ n -> collectElements (Just n) i ts
			   _ -> error "listElements"

print_Literal_text :: GlobalAnnos -> Id -> [TERM] -> Doc
print_Literal_text =
    print_Literal printText0 parens (<+>) fsep (commaT_text)
		  (char '.') (char 'E')

print_Literal_latex :: GlobalAnnos -> Id -> [TERM] -> Doc
print_Literal_latex =
    print_Literal printLatex0 parens_latex
		  (<\+>) fsep_latex (commaT_latex)
		  (casl_normal_latex ".") (casl_normal_latex "E")

-- printing consitent mixfix application or predication
{- TODO: consider string-, number-, list- and floating-annotations -}
print_mixfix_appl :: (forall a .PrettyPrint a => GlobalAnnos -> a -> Doc)
		  -> (Doc -> Doc)   -- ^ a function that surrounds 
				     -- the given Doc with appropiate 
				     -- parens
		  -> (Doc -> Doc -> Doc)    -- ^ a beside with space 
					    -- like <+> or <\+>
		  -> ([Doc] -> Doc)    -- ^ a list concat with space and 
				       -- fill the line policy  like
				       -- fsep or fsep_latex
		  -> GlobalAnnos -> Id -> [TERM] -> Doc
print_mixfix_appl pf parens_fun 
		  beside_fun fsep_fun 
		  ga oid terms = 
		      d_terms_b_comp <> c `beside_fun` d_terms_a_comp
    where (tops,cs) = case oid of Id x1 x2 _ -> (x1,x2)
	  c = if null cs then text "" -- an empty String works for ASCII 
				      -- and LaTeX ensuring a space after 
				      -- the last token of the identifier 
				      -- if the compound is empty
	      else pf ga (Id [] cs [])
          (tps_b_comp,places) = splitMixToken tops
	  nr_places = length $ filter isPlace tps_b_comp
	  (terms_b_comp,terms_a_comp) = splitAt nr_places terms
	  d_terms_b_comp = fsep_fun (first_term 
				     : fillIn tps_b_comp' terms_b_comp')
	  d_terms_a_comp = fsep_fun (fillIn places' terms_a_comp'
				     ++ [last_term])
	  isL3 = length tops >= 3
	  tps_b_comp' :: [Token]
	  terms_b_comp' :: [TERM]
	  first_term    :: Doc
	  (tps_b_comp',terms_b_comp',first_term) = 
	      if isL3 && (isPlace $ head tps_b_comp) 
	      then
	         (tail tps_b_comp,
		  tail terms_b_comp,
		  condParensAppl pf parens_fun 
		                 ga oid (head terms_b_comp)
		                 (Just ALeft))
	      else
	         (tps_b_comp,terms_b_comp,empty)
	  (places',terms_a_comp',last_term) = 
	      if isL3 && (not $ null places)  
	      then
	         (init places,init terms_a_comp,
		  condParensAppl pf parens_fun
		                 ga oid (last terms_a_comp) 
		                 (Just ARight))
	      else
	         (places,terms_a_comp,empty)
	  fillIn :: [Token] -> [TERM] -> [Doc]
	  fillIn tps ts = let (_,nl) = mapAccumL pr ts tps in nl
	  pr :: [TERM] -> Token -> ([TERM],Doc)
	  pr [] top = ([], pf ga top)
	  pr tS@(t:ts) top 
	      | isPlace top = (ts,pf ga t)
	      | otherwise   = (tS,pf ga top)

condParensAppl :: (GlobalAnnos -> TERM -> Doc)
	       -> (Doc -> Doc)    -- ^ a function that surrounds 
				  -- the given Doc with appropiate 
				  -- parens
	       -> GlobalAnnos -> Id -> TERM -> Maybe AssocEither -> Doc
condParensAppl pf parens_fun ga o_i t mdir = 
    case t of
    Simple_id _ -> t'
    Application _ [] _ -> t'
    Application o it _
	| isLiteral ga i_i it -> t'
        -- ordinary appl (no place)
	| isOrdAppl i_i -> t' 
	-- postfix appl
	| isOrdAppl o_i && isPostfix i_i -> t' 
	| isMixfix  o_i && isPostfix i_i -> t' 
	-- prefix appl w/o parens
	| isOrdAppl o_i && isPrefix i_i  -> t'
	| isPostfix o_i && isPrefix i_i  -> parens_fun t'
	-- infix appl (left and right arg/place)
	|    (isInfix i_i && isSurround o_i)
	  || (isInfix o_i && isSurround i_i) -> t'
	| isInfix i_i && o_i == i_i -> 
	    case mdir of
		      Nothing -> condParensPrec 
		      Just ALeft | isLAssoc amap o_i -> t'
				 | otherwise -> parens_fun t'
		      Just ARight | isRAssoc amap o_i -> t'
				  | otherwise -> parens_fun t'
	| otherwise -> condParensPrec 
    	where i_i = case o of
			  Op_name i          -> i
			  Qual_op_name i _ _ -> i
	      condParensPrec = case precRel (prec_annos ga) o_i i_i of
			       Lower       -> t'
			       _ -> parens_fun t'
	      amap = assoc_annos ga
    Sorted_term _ _ _ -> t'
    Cast _ _ _ -> t'
    _ -> parens_fun t'
    where t' = pf ga t


condParensImplEquiv :: (GlobalAnnos -> FORMULA -> Doc)
		    -> (Doc -> Doc)    -- ^ a function that surrounds 
				       -- the given Doc with appropiate 
				       -- parens
		    -> GlobalAnnos -> FORMULA -> FORMULA -> Doc
condParensImplEquiv pf parens_fun ga e_i f =  
    case e_i of 
    Implication _ _ _ -> case f of Implication _ _ _ -> f'
				   Disjunction _ _ -> f'
				   Conjunction _ _ -> f'
				   Negation _ _ -> f' 
				   True_atom _  -> f' 
				   False_atom _ -> f'
				   Predication _ _ _ -> f' 
				   Existl_equation _ _ _ -> f'
				   Strong_equation _ _ _ -> f'
				   _           -> parens_fun f'
    Equivalence _ _ _ -> case f of Disjunction _ _ -> f'
				   Conjunction _ _ -> f'
				   Negation _ _ -> f' 
				   True_atom _  -> f' 
				   False_atom _ -> f'
				   Predication _ _ _ -> f'
				   Quantification _ _ _ _ -> f'
				   Existl_equation _ _ _ -> f'
				   Strong_equation _ _ _ -> f'
				   _           -> parens_fun f'
    _ ->  error "Wrong call: condParensImplEquiv"
    where f' = pf ga f
condParensXjunction :: (GlobalAnnos -> FORMULA -> Doc)
		    -> (Doc -> Doc)    -- ^ a function that surrounds 
				       -- the given Doc with appropiate 
				       -- parens
		    -> GlobalAnnos -> FORMULA -> Doc
condParensXjunction pf parens_fun ga x = 
    case x of Negation _ _ -> x' 
	      True_atom _  -> x' 
	      False_atom _ -> x'
	      Predication _ _ _ -> x'
	      Existl_equation _ _ _ -> x'
	      Strong_equation _ _ _ -> x'
	      _            -> parens_fun x' 
    where x' = pf ga x


---- instances of ListCheck for various data types of AS_Basic_CASL ---
instance ListCheck SIG_ITEMS where
    (Sort_items l _)     `innerListGT` i = length l > i
    (Op_items l _)       `innerListGT` i = length l > i
    (Pred_items l _)     `innerListGT` i = length l > i
    (Datatype_items l _) `innerListGT` i = length l > i

instance ListCheck SORT_ITEM where
    (Sort_decl l _)          `innerListGT` i = length l > i
    (Subsort_decl l _ _)     `innerListGT` i = length l > i
    (Subsort_defn _ _ _ _ _) `innerListGT` _ = False
    (Iso_decl _ _)           `innerListGT` _ = False


instance ListCheck OP_ITEM where
    (Op_decl l _ _ _) `innerListGT` i = length l > i
    (Op_defn _ _ _ _) `innerListGT` _ = False

instance ListCheck PRED_ITEM where
    (Pred_decl l _ _)   `innerListGT` i = length l > i
    (Pred_defn _ _ _ _) `innerListGT` _ = False

instance ListCheck DATATYPE_DECL where
    (Datatype_decl _ _ _) `innerListGT` _ = False

instance ListCheck VAR_DECL where
    (Var_decl l _ _) `innerListGT` i = length l > i


-----------------------------------------------------------------------------
