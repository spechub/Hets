{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Christian Maeder and Uni Bremen 2002-2003 
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable

pretty printing data types of 'BASIC_SPEC'

-}

module CASL.Print_AS_Basic where

import Data.List (mapAccumL)

import Common.Id
import CASL.AS_Basic_CASL
import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.ConvertLiteral
import CASL.LiteralFuns
import CASL.Utils

import Common.Print_AS_Annotation

import Common.Keywords
import Common.Lib.Pretty
import Common.PrettyPrint
import Common.PPUtils

instance (PrettyPrint b, PrettyPrint s, PrettyPrint f) =>
    PrettyPrint (BASIC_SPEC b s f) where
    printText0 ga (Basic_spec l) = 
	if null l then braces empty else vcat (map (printText0 ga) l) 

instance (PrettyPrint b, PrettyPrint s, PrettyPrint f) =>
    PrettyPrint (BASIC_ITEMS b s f) where
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
    printText0 ga (Local_var_axioms l f _) = 
	text forallS <+> semiT_text ga l
		 $$ printFormulaAux ga f
    printText0 ga (Axiom_items f _) = 
	printFormulaAux ga f
    printText0 ga (Ext_BASIC_ITEMS b) = printText0 ga b

printFormulaAux :: PrettyPrint f => GlobalAnnos -> [Annoted (FORMULA f)] -> Doc
printFormulaAux ga f =
  vcat $ map (printAnnotedFormula_Text0 ga True) f

printAnnotedFormula_Text0 :: PrettyPrint f => 
			     GlobalAnnos -> Bool ->  Annoted (FORMULA f) -> Doc
printAnnotedFormula_Text0 ga withDot (Annoted i _ las ras) =
        let i'   = -- trace (show i) $ 
		 (if withDot then (char '.' <+>) else id) $  
		 printFORMULA ga i
	    las' = if not $ null las then 
	               ptext "\n" <> printAnnotationList_Text0 ga las
		   else
		       empty
	    (la,ras') = splitAndPrintRAnnos printText0 
				    printAnnotationList_Text0 
				    (<+>) id empty ga ras
        in las' $+$ (hang i' 0 la) $$ ras'

instance (PrettyPrint s, PrettyPrint f) =>
         PrettyPrint (SIG_ITEMS s f) where
    printText0 ga (Sort_items l _) =  
	text sortS<>pluralS_doc l <+> semiAnno_text ga l
    printText0 ga (Op_items l _) =  
	text opS<>pluralS_doc l <+> semiAnno_text ga l 
    printText0 ga (Pred_items l _) =  
	text predS<>pluralS_doc l <+> semiAnno_text ga l 
    printText0 ga (Datatype_items l _) = 
	text typeS<>pluralS_doc l <+> semiAnno_text ga l 
    printText0 ga (Ext_SIG_ITEMS s) = printText0 ga s

instance PrettyPrint f =>
         PrettyPrint (SORT_ITEM f) where
    printText0 ga (Sort_decl l _) = commaT_text ga l
    printText0 ga (Subsort_decl l t _) = 
	hang (commaT_text ga l) 4 $ text lessS <+> printText0 ga t
    printText0 ga (Subsort_defn s v t f _) = 
	-- TODO: lannos of f should printed after the equal sign 
	printText0 ga s <+> ptext equalS <+> 
	   braces (hang (printText0 ga v <+> colon <+> printText0 ga t) 
		         4 (char '.' <+> printFORMULA ga (item f)))
    printText0 ga (Iso_decl l _) = 
	fsep $ punctuate  (space <>text equalS) $ map (printText0 ga) l


instance PrettyPrint f => PrettyPrint (OP_ITEM f) where
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

optQuMark :: FunKind -> Doc
optQuMark Partial = text quMark
optQuMark Total = empty

instance PrettyPrint OP_TYPE where
    printText0 ga (Op_type k l s _) = (if null l then empty
					   else space 
					        <> crossT_text ga l 
				                <+> text funS)
				           <> optQuMark k
                                           <> space <> printText0 ga s

instance PrettyPrint OP_HEAD where
    printText0 ga (Op_head k l s _) = 
	(if null l then empty 
	 else parens(semiT_text ga l))
	<> colon <> optQuMark k
	<+> printText0 ga s

instance PrettyPrint ARG_DECL where
    printText0 ga (Arg_decl l s _) = commaT_text ga l 
			      <+> colon
			      <> printText0 ga s

instance PrettyPrint f => PrettyPrint (OP_ATTR f) where
    printText0 _ (Assoc_op_attr)   = text assocS
    printText0 _ (Comm_op_attr)    = text commS 
    printText0 _ (Idem_op_attr)    = text idemS
    printText0 ga (Unit_op_attr t) = text unitS <+> printText0 ga t

instance PrettyPrint f => PrettyPrint (PRED_ITEM f) where
    printText0 ga (Pred_decl l t _) = commaT_text ga l 
				  <+> colon <+> printText0 ga t
    printText0 ga (Pred_defn n h f _) = printText0 ga n 
				        <> printText0 ga h
                                        <+> text equivS
				        <+> printFORMULA ga (item f)

instance PrettyPrint PRED_TYPE where
    printText0 _ (Pred_type [] _) = parens empty
    printText0 ga (Pred_type l _) = crossT_text ga l

instance PrettyPrint PRED_HEAD where
    printText0 ga (Pred_head l _) = parens (semiT_text ga l)

instance PrettyPrint DATATYPE_DECL where
    printText0 ga (Datatype_decl s a _) = case a of 
        h : t -> printText0 ga s <+> 
	    sep ((hang (text defnS) 4 (printText0 ga h)):
	     (map (\x -> nest 2 $ ptext barS <+> nest 2 (printText0 ga x)) t))
        [] -> error "PrettyPrint CASL.DATATYPE_DECL"

instance PrettyPrint ALTERNATIVE where
    printText0 ga (Alt_construct k n l _) = printText0 ga n 
				 <> (if null l then case k of 
                                                   Partial -> parens empty
                                                   _ -> empty
				    else parens(semiT_text ga l)) 
                                 <> optQuMark k
    printText0 ga (Subsorts l _) = 
	text (sortS++pluralS l) <+> commaT_text ga l 

instance PrettyPrint COMPONENTS where
    printText0 ga (Cons_select k l s _) = commaT_text ga l 
				<> colon <> optQuMark k
				<> printText0 ga s 
    printText0 ga (Sort s) = printText0 ga s 	  

instance PrettyPrint VAR_DECL where
    printText0 ga (Var_decl l s _) = commaT_text ga l 
				<> colon 
				<+> printText0 ga s 

printFORMULA :: PrettyPrint f => GlobalAnnos -> FORMULA f -> Doc
printFORMULA ga (Quantification q l f _) = 
	hang (printText0 ga q <+> semiT_text ga l) 4 $ 
	     char '.' <+> printFORMULA ga f
printFORMULA ga (Conjunction l _) = 
	sep $ prepPunctuate (ptext lAnd <> space) $ 
	    map (condParensXjunction printFORMULA parens ga) l
printFORMULA ga (Disjunction  l _) = 
	sep $ prepPunctuate (ptext lOr <> space) $ 
	    map (condParensXjunction printFORMULA parens ga) l
printFORMULA ga i@(Implication f g isArrow _) = 
	if isArrow
	then (
              hang (condParensImplEquiv printFORMULA parens ga i f False
		    <+> ptext implS) 4 $ 
	      condParensImplEquiv printFORMULA parens ga i g True)
	else (
              hang (condParensImplEquiv printFORMULA parens ga i g False
		    <+> ptext "if") 4 $ 
	      condParensImplEquiv printFORMULA parens ga i f True)
printFORMULA ga e@(Equivalence  f g _) = 
	hang (condParensImplEquiv printFORMULA parens ga e f False
	      <+> ptext equivS) 4 $
	     condParensImplEquiv printFORMULA parens ga e g True
printFORMULA ga (Negation f _) = 
    ptext "not" <+> condParensNeg f parens (printFORMULA ga f)
printFORMULA _ (True_atom _)  = ptext trueS
printFORMULA _ (False_atom _) = ptext falseS
printFORMULA ga (Predication p l _) = 
	let (p_id,isQual) = 
		case p of
		       Pred_name i          -> (i,False)
		       Qual_pred_name i _ _ -> (i,True)
	    p' = printText0 ga p
	in if isQual then 
	     print_prefix_appl_text ga p' l  
	   else condPrint_Mixfix_text ga p_id l
printFORMULA ga (Definedness f _) = text defS <+> printText0 ga f
printFORMULA ga (Existl_equation f g _) = 
	hang (printText0 ga f <+> ptext exEqual) 4 $ printText0 ga g
printFORMULA ga (Strong_equation f g _) = 
	hang (printText0 ga f <+> ptext equalS) 4 $ printText0 ga g 
printFORMULA ga (Membership f g _) = 
	printText0 ga f <+> ptext inS <+> printText0 ga g
printFORMULA ga (Mixfix_formula t) = {- trace ("Mixfix_formula found: "
                                            ++ showPretty t "") $ -}
					printText0 ga t
printFORMULA _ (Unparsed_formula s _) = text s 
printFORMULA ga (Sort_gen_ax constrs _) = 
        text generatedS <> 
        braces (text sortS <+> commaT_text ga sorts 
                <> semi <+> semiT_text ga ops)
         <+> (if null sortMap then empty
               else text withS 
                <+> fsep (punctuate comma (map printSortMap sortMap)))
        where (sorts,ops,sortMap) = recover_Sort_gen_ax constrs
              printSortMap (s1,s2) =
                printText0 ga s1 <+> ptext "|->" <+> printText0 ga s2
printFORMULA ga (ExtFORMULA f) = printText0 ga f

instance PrettyPrint f => PrettyPrint (FORMULA f) where
    printText0 ga f@(Sort_gen_ax _ _) = printFORMULA ga f
    printText0 ga f = ptext " . " <> printFORMULA ga f


instance PrettyPrint QUANTIFIER where
    printText0 _ (Universal) = ptext forallS
    printText0 _ (Existential) = ptext existsS
    printText0 _ (Unique_existential) = ptext (existsS ++ exMark)

instance PrettyPrint PRED_SYMB where
    printText0 ga (Pred_name n) = printText0 ga n
    printText0 ga (Qual_pred_name n t _) = 
	parens $ ptext predS <+> printText0 ga n <+> colon <+> printText0 ga t

instance PrettyPrint f => PrettyPrint (TERM f) where
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
	     print_prefix_appl_text ga (parens o') l
	   else print_Literal_text ga o_id l
    printText0 ga (Sorted_term t s _) = 
        condParensSorted_term parens t (printText0 ga t) <> 
        colon <+> printText0 ga s
    printText0 ga (Cast t s _) = 
        printText0 ga t <+> text asS <+> printText0 ga s
    printText0 ga(Conditional u f v _) = 
	hang (printText0 ga u) 4 $ 
	     sep ((text whenS <+> printFORMULA ga f):
		     [text elseS <+> printText0 ga v])
    printText0 _ (Unparsed_term s _) = text s
    printText0 ga (Mixfix_qual_pred p) = printText0 ga p
    printText0 ga (Mixfix_term [o, a@(Mixfix_parenthesized _ _)]) =
        printText0 ga o <> printText0 ga a 
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

instance PrettyPrint OP_SYMB where
    printText0 ga (Op_name o) = printText0 ga o
    printText0 ga (Qual_op_name o t _) = 
	text opS <+> printText0 ga o <+> colon <> printText0 ga t

instance PrettyPrint SYMB_ITEMS where
    printText0 ga (Symb_items k l _) = 
	printText0 ga k <> ptext (pluralS_symb_list k l) 
		        <+> commaT_text ga l

instance PrettyPrint SYMB_ITEMS_LIST where
    printText0 ga (Symb_items_list l _) = commaT_text ga l

instance PrettyPrint SYMB_MAP_ITEMS where
    printText0 ga (Symb_map_items k l _) = 
	printText0 ga k <> ptext (pluralS_symb_list k l) 
		        <+> commaT_text ga l

instance PrettyPrint SYMB_MAP_ITEMS_LIST where 
    printText0 ga (Symb_map_items_list l _) = commaT_text ga l

instance PrettyPrint SYMB_KIND where 
    printText0 _ Implicit   = empty
    printText0 _ Sorts_kind = ptext sortS
    printText0 _ Ops_kind   = ptext opS
    printText0 _ Preds_kind = ptext predS

instance PrettyPrint SYMB where 
    printText0 ga (Symb_id i) = printText0 ga i
    printText0 ga (Qual_id i t _) = 
	printText0 ga i <+> colon <+> printText0 ga t

instance PrettyPrint TYPE where 
    printText0 ga (O_type t) = printText0 ga t
    printText0 ga (P_type t) = printText0 ga t
    printText0 ga (A_type t) = printText0 ga t

instance PrettyPrint SYMB_OR_MAP where 
    printText0 ga (Symb s) = printText0 ga s
    printText0 ga (Symb_map s t _) = 
	printText0 ga s <+> text mapsTo <+> printText0 ga t

---- helpers ----------------------------------------------------------------

pluralS_symb_list :: SYMB_KIND -> [a] -> String
pluralS_symb_list k l = case k of
		       Implicit -> ""
		       _        -> if length l > 1 
				   then "s" 
				   else ""

condPrint_Mixfix :: (Token -> Doc)
		 -> (Id -> Doc)
		 -> (TERM f -> Doc)
		 -> (Doc -> Doc)    -- ^ a function that surrounds 
				    -- the given Doc with appropiate 
				    -- parens
		 -> (Doc -> Doc -> Doc) -- ^ a beside with space 
					-- like <+> or <\+>
		 -> ([Doc] -> Doc)    -- ^ a list concat with space and 
				      -- fill the line policy  like
				      -- fsep or fsep_latex
		 -> Doc -- comma doc
		 -> Maybe (Token -> Doc) -- ^ this function should be 
					 -- given to print a Token in a 
					 -- special way 
		 -> (Maybe Display_format)
		 ->  GlobalAnnos -> Id -> [TERM f] -> Doc
condPrint_Mixfix pTok pId pTrm parens_fun
		 beside_fun fsep_fun comma_doc mpt_fun mdf
		 ga i l =
    if isMixfix dispId
    then
       if placeCount dispId == length l
       then
	  print_mixfix_appl pTok pId pTrm parens_fun 
			    beside_fun fsep_fun mpt_fun 
	                    (not $ null dispToks) ga dispId l 
       else 
          print_prefix_appl pTrm parens_fun fsep_fun comma_doc o' l
    else print_prefix_appl pTrm parens_fun fsep_fun comma_doc (pId i) l
    where o' = if null dispToks then pId i else dispIdDoc
	  dispIdDoc = 
	      fsep_fun $ (maybe (map pTok) (\f -> map f) (mpt_fun)) dispToks
	  dispToks = maybe [] (\x -> maybe [] id (lookupDisplay ga x i)) mdf
	     -- null if no display entry is available
	  dispId = if null dispToks then i else Id dispToks [] nullRange
{- TODO: consider string-, number-, list- and floating-annotations -}

condPrint_Mixfix_text :: PrettyPrint f => GlobalAnnos -> Id -> [TERM f] -> Doc
condPrint_Mixfix_text ga =
    condPrint_Mixfix (printText0 ga) (printText0 ga) 
		  (printText0 ga) parens 
		     (<+>) fsep comma Nothing Nothing ga

-- printing consitent mixfix application or predication
{- TODO: consider string-, number-, list- and floating-annotations -}
print_mixfix_appl :: (Token -> Doc)  -- ^ print a Token
		  -> (Id -> Doc)     -- ^ print an Id
		  -> (TERM f -> Doc)   -- ^ print TERM recursively 	 
		  -> (Doc -> Doc)   -- ^ a function that surrounds 
				     -- the given Doc with appropiate 
				     -- parens
		  -> (Doc -> Doc -> Doc)    -- ^ a beside with space 
					    -- like <+> or <\+>
		  -> ([Doc] -> Doc)    -- ^ a list concat with space and 
				       -- fill the line policy  like
				       -- fsep or fsep_latex
		  -> Maybe (Token -> Doc) -- ^ this function should be 
					  -- given to print a Token in a 
					  -- special way if Nothing is given
					  -- pf is used
		  -> Bool -- ^ True if a display_annotation 
			  -- has generated this Id
		  -> GlobalAnnos -> Id -> [TERM f] -> Doc
print_mixfix_appl pTok pId pTrm parens_fun 
		  beside_fun fsep_fun 
		  mpt_fun isDisplayAnnoModi
		  ga oid terms = 
		      d_terms_b_comp <> c `beside_fun` d_terms_a_comp
    where (tops,cs) = case oid of Id x1 x2 _ -> (x1,x2)
	  c = if null cs then text "" -- an empty String works for ASCII 
				      -- and LaTeX ensuring a space after 
				      -- the last token of the identifier 
				      -- if the compound is empty
	      else pId (Id [] cs nullRange)
          (tps_b_comp,places) = splitMixToken tops
	  nr_places = length $ filter isPlace tps_b_comp
	  (terms_b_comp,terms_a_comp) = splitAt nr_places terms
	  d_terms_b_comp = fsep_fun (first_term 
				     : fillIn tps_b_comp' terms_b_comp')
	  d_terms_a_comp = fsep_fun (fillIn places' terms_a_comp'
				     ++ [last_term])
	  -- tps_b_comp' :: [Token]
	  -- terms_b_comp' :: PrettyPrint f => [TERM f]
	  -- first_term  :: Doc
	  (tps_b_comp',terms_b_comp',first_term) = 
	      if null tps_b_comp then -- invisible Id 
		([], terms_b_comp, empty) 
	      else if (isPlace $ head tps_b_comp) 
	      then
	         (tail tps_b_comp,
		  tail terms_b_comp,
		  condParensAppl pTrm parens_fun 
		                 ga oid (head terms_b_comp)
		                 (Just ALeft))
	      else
	         (tps_b_comp,terms_b_comp,empty)
	  (places',terms_a_comp',last_term) = 
	      if (not $ null places)  
	      then
	         (init places,init terms_a_comp,
		  condParensAppl pTrm parens_fun
		                 ga oid (last terms_a_comp) 
		                 (Just ARight))
	      else
	         (places,terms_a_comp,empty)
	  -- fillIn :: PrettyPrint f => [Token] -> [TERM f] -> [Doc]
	  fillIn tps ts = let (_,nl) = mapAccumL pr ts tps in nl
	  -- pr :: PrettyPrint f => [TERM f] -> Token -> ([TERM f],Doc)
	  pr [] top = ([], pf' top)
	  pr tS@(t:ts) top 
	      | isPlace top = (ts, pTrm t)
	      | otherwise   = (tS,pf' top)
	  pf' = maybe pTok 
		      (\ f -> if isDisplayAnnoModi 
		              then f 
		              else pTok) 
		      mpt_fun

-- printing consistent prefix application and predication
print_prefix_appl :: (TERM f -> Doc)   -- ^ print TERM recursively 
		  -> (Doc -> Doc)    -- ^ a function that surrounds 
				     -- the given Doc with appropiate 
				     -- parens
	          -> ([Doc] -> Doc)    -- ^ a list concat without space and 
				   -- fill the line policy  like
				   -- fsep or fsep_latex
		  -> Doc -- ^ comma
		  -> Doc -> [TERM f] -> Doc 
print_prefix_appl pTrm parens_fun fsep_fun comma_doc po' l = po' <> 
            (if null l then empty 
	     else parens_fun $ fsep_fun $ punctuate comma_doc $ map pTrm l)

print_prefix_appl_text :: PrettyPrint f => GlobalAnnos -> Doc -> [TERM f] -> Doc
print_prefix_appl_text ga =
    print_prefix_appl (printText0 ga) parens fsep comma

print_Literal :: (Token -> Doc)  -- ^ print a Token
              -> (Id -> Doc)     -- ^ print an Id
	      -> (TERM f -> Doc)   -- ^ print TERM recursively 	 
	      -> (Doc -> Doc)    -- ^ a function that surrounds 
				 -- the given Doc with appropiate 
				 -- parens
	      -> (Doc -> Doc -> Doc)    -- ^ a beside with space 
					-- like <+> or <\+>
	      -> ([Doc] -> Doc)    -- ^ a list concat without space and 
				   -- fill the line policy  like
				   -- fsep or fsep_latex
	      -> Doc   -- ^ a comma 
	      -> Maybe (Token -> Doc) -- ^ this function should be 
				      -- given to print a Token in a 
				      -- special way 
	      -> (Maybe Display_format)
	      -> GlobalAnnos -> Id -> [TERM f] -> Doc
print_Literal pTok pId pTrm parens_fun 
	      beside_fun fsep_fun comma_doc mpt_fun mdf
	      ga i ts =  
    if isList ga i ts then
       let list_body = fsep_fun $ punctuate comma_doc $ map pTrm 
                       $ getListElems splitAppl ts 
	   (openL, closeL, comps) = getListBrackets $ 
                case getLiteralType ga i of
		ListNull b -> b
		ListCons b _ -> b
		_ -> error "print_Literal_text"
        in hcat(map pTok openL) <+> list_body 
			     <+> hcat(map pTok closeL)
			     <> pId (Id [] comps nullRange)
    else if isNumber ga i ts then
         pTok $ toNumber splitAppl i ts
    else if isFrac ga i ts then
         pTok $ toFrac splitAppl ts
    else if isFloat ga i ts then
         pTok $ toFloat splitAppl ga ts 
    else if isString ga i ts then 
        pTok $ Token ( "\"" ++ toString splitAppl ga i ts ++ "\"") nullRange
    else condPrint_Mixfix pTok pId pTrm parens_fun 
	      beside_fun fsep_fun comma_doc mpt_fun mdf ga i ts

print_Literal_text :: PrettyPrint f => GlobalAnnos -> Id -> [TERM f] -> Doc
print_Literal_text ga = print_Literal (printText0 ga) (printText0 ga) 
    (printText0 ga) parens (<+>) fsep comma Nothing Nothing ga

condParensAppl :: (TERM f -> Doc)
	       -> (Doc -> Doc)    -- ^ a function that surrounds 
				  -- the given Doc with appropiate 
				  -- parens
	       -> GlobalAnnos -> Id -> TERM f -> Maybe AssocEither -> Doc
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
	-- prefix appl w/o parens
	| isOrdAppl o_i && isPrefix  i_i -> t'
	-- both mixfix and in <> prec relation so parens
	| isMixfix o_i && isMixfix i_i 
	  && explicitGrouping o_i i_i    -> parens_fun t'
	| isPostfix o_i && isPrefix  i_i -> parens_fun t'
	| isPrefix  o_i && isPostfix i_i -> t'
	| isPrefix  o_i && isInfix   i_i -> parens_fun t'
	| isInfix   o_i && isPrefix  i_i -> t'
	| isInfix   o_i && isPostfix i_i -> t'
	-- infix appl (left and right arg/place)
	|    (isInfix i_i && isSurround o_i)
	  || (isInfix o_i && isSurround i_i) -> t'
	| isInfix i_i && o_i == i_i -> 
	    case mdir of
		      Nothing -> condParensPrec 
		      Just ass | isAssoc ass amap o_i -> t'
			       | otherwise -> parens_fun t'
	| otherwise -> condParensPrec 
    	where i_i = op_id o
	      condParensPrec = case precRel (prec_annos ga) o_i i_i of
			       Lower -> t'
			       _     -> parens_fun t'
	      amap = assoc_annos ga
	      explicitGrouping :: Id -> Id -> Bool
	      explicitGrouping i1 i2 = 
		  case precRel (prec_annos ga) i1 i2 of
		  BothDirections -> True
		  _              -> False
    Sorted_term _ _ _ -> t'
    Cast _ _ _ -> t'
    _ -> parens_fun t'
    where t' = pf t

condParensSorted_term :: (Doc -> Doc) 
                         -- ^ a function that surrounds 
			 -- the given Doc with appropiate 
			 -- parens
                      -> TERM f -> Doc -> Doc
condParensSorted_term  parens_fun t = 
    case t of
    Application osy l _ 
        | null l     -> id
        | isQualOpSy osy -> id
        | not (isMixfix (op_id osy)) -> id
        | otherwise -> parens_fun
    _ 
        | isMixfixTerm t -> parens_fun
        | otherwise      -> id

is_atomic_FORMULA :: FORMULA f -> Bool
is_atomic_FORMULA f =
    case f of 
	   True_atom _  -> True 
	   False_atom _ -> True
	   Predication _ _ _ -> True 
	   Existl_equation _ _ _ -> True
	   Definedness _ _ -> True
	   Strong_equation _ _ _ -> True
	   Membership _ _ _ -> True
	   _ -> False

condParensNeg :: FORMULA f -> (Doc -> Doc) -> Doc -> Doc
condParensNeg f parens_fun =
    if is_atomic_FORMULA f then id else parens_fun


condParensXjunction :: (GlobalAnnos -> FORMULA f -> Doc)
		    -> (Doc -> Doc)    -- ^ a function that surrounds 
				       -- the given Doc with appropiate 
				       -- parens
		    -> GlobalAnnos -> FORMULA f -> Doc
condParensXjunction pf parens_fun ga x = 
    case x of 
	   Negation _ _ -> x' 
	   ExtFORMULA _ -> x'
	   _ | is_atomic_FORMULA x -> x'
	     | otherwise -> parens_fun x' 
    where x' = pf ga x


condParensImplEquiv :: (GlobalAnnos -> FORMULA f -> Doc)
		    -> (Doc -> Doc)    -- ^ a function that surrounds 
				       -- the given Doc with appropiate 
				       -- parens
		    -> GlobalAnnos -> FORMULA f 
		    -> FORMULA f 
		    -> Bool -- ^ True if second FORMULA f arg is 
			    -- right of the connective in the first 
			    -- FORMULA f arg
		    -> Doc
condParensImplEquiv pf parens_fun ga e_i f isRight =  
    case e_i of 
    Implication _ _ isArrow1 _ -> 
	case f of 
	Implication _ _ isArrow2 _ 
	    | isArrow1 == isArrow2 -> f'
	    | otherwise -> parens_fun f'
	Quantification _ _ _ _ 
	    | isRight   -> f'
	    | otherwise -> parens_fun f'
	_ | has_higher_prec f -> f'
	  | otherwise -> parens_fun f'
    Equivalence _ _ _   -> 
	case f of
	_ | has_higher_prec f -> f'
	  | otherwise -> parens_fun f'
    _ ->  error "Wrong call: condParensImplEquiv"
    where f' = pf ga f
	  has_higher_prec ff = 
	      case ff of
	      Negation _ _ -> True
	      ExtFORMULA _ -> True
	      Disjunction _ _ -> True
	      Conjunction _ _ -> True
	      _ -> is_atomic_FORMULA ff


---- instances of ListCheck for various data types of AS_Basic_CASL ---
instance ListCheck (SIG_ITEMS s f) where
    (Sort_items l _)     `innerListGT` i = length l > i
    (Op_items l _)       `innerListGT` i = length l > i
    (Pred_items l _)     `innerListGT` i = length l > i
    (Datatype_items l _) `innerListGT` i = length l > i
    (Ext_SIG_ITEMS _)    `innerListGT` _ = False        

instance ListCheck (SORT_ITEM f) where
    (Sort_decl l _)          `innerListGT` i = length l > i
    (Subsort_decl l _ _)     `innerListGT` i = length l > i
    (Subsort_defn _ _ _ _ _) `innerListGT` _ = False
    (Iso_decl _ _)           `innerListGT` _ = False

instance ListCheck (OP_ITEM f) where
    (Op_decl l _ _ _) `innerListGT` i = length l > i
    (Op_defn _ _ _ _) `innerListGT` _ = False

instance ListCheck (PRED_ITEM f) where
    (Pred_decl l _ _)   `innerListGT` i = length l > i
    (Pred_defn _ _ _ _) `innerListGT` _ = False

instance ListCheck DATATYPE_DECL where
    (Datatype_decl _ _ _) `innerListGT` _ = False

instance ListCheck VAR_DECL where
    (Var_decl l _ _) `innerListGT` i = length l > i

-----------------------------------------------------------------------------
