
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

module Print_AS_Basic where

-- debugging
import IOExts (trace)

import List (mapAccumL)

import Id
import AS_Basic_CASL
import AS_Annotation
import GlobalAnnotations
import GlobalAnnotationsFunctions (precRel,isLAssoc,isRAssoc,isLiteral
				  ,getLiteralType
				  )

import Print_AS_Annotation

import Keywords
import Pretty
import PrettyPrint
import PPUtils

instance PrettyPrint BASIC_SPEC where
    printText0 ga (Basic_spec l) = 
	if null l then braces empty else vcat (map (printText0 ga) l) 

instance PrettyPrint BASIC_ITEMS where
    printText0 ga (Sig_items s) = printText0 ga s
    printText0 ga (Free_datatype l _) = 
	hang (ptext freeS <+> ptext typeS<>pluralS l) 4 $ 
	     semiAnno printText0 ga l
    printText0 ga (Sort_gen l _) = 
	hang (ptext generatedS <+> condTypeS) 4 $ 
	     condBraces (vcat (map (printText0 ga) l))
	where condTypeS = 
		  if isOnlyDatatype then ptext typeS<>pluralS l 
		  else empty
	      condBraces d = 
		  if isOnlyDatatype then 
		     case l of
		     [x] -> case x of
			    Annoted (Datatype_items l' _) _ lans _ -> 
				printText0 ga lans $$ semiAnno printText0 ga l'
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
	text varS<>pluralS l <+> semiT printText0 ga l
    printText0 ga (Local_var_axioms l f p) = 
	text forallS <+> semiT printText0 ga l
		 $$ printText0 ga (Axiom_items f p)
    printText0 ga (Axiom_items f _) = 
	vcat $ map (\x -> char '.' <+> printText0 ga x) f

instance PrettyPrint SIG_ITEMS where
    printText0 ga (Sort_items l _) =  
	text sortS<>pluralS l <+> semiAnno printText0 ga l
    printText0 ga (Op_items l _) =  
	text opS<>pluralS l <+> semiAnno printText0 ga l 
    printText0 ga (Pred_items l _) =  
	text predS<>pluralS l <+> semiAnno printText0 ga l 
    printText0 ga (Datatype_items l _) = 
	text typeS<>pluralS l <+> semiAnno printText0 ga l 

instance PrettyPrint SORT_ITEM where
    printText0 ga (Sort_decl l _) = commaT printText0 ga l
    printText0 ga (Subsort_decl l t _) = 
	hang (commaT printText0 ga l) 4 $ text lessS <+> printText0 ga t
    printText0 ga (Subsort_defn s v t f _) = 
	{- TODO: lannos of f should printed after the equal sign -}
	printText0 ga s <+> ptext equalS <+> 
	   braces (hang (printText0 ga v <+> colon <+> printText0 ga t) 
		         4 (ptext "." <+> printText0 ga f))
    printText0 ga (Iso_decl l _) = 
	fsep $ punctuate  (space <>text equalS) $ map (printText0 ga) l

instance PrettyPrint OP_ITEM where
    printText0 ga (Op_decl l t a _) = 
	hang (hang (commaT printText0 ga l) 
	            4 
	            (colon <> printText0 ga t <> condComma)) 
             4 $
	       if na then empty 
	       else commaT printText0 ga a
	where na = null a
	      condComma = if na then empty
			  else comma
    printText0 ga (Op_defn n h t _) = printText0 ga n 
				  <> printText0 ga h
                                  <+> text equalS
				  <+> printText0 ga t

instance PrettyPrint OP_TYPE where
    printText0 ga (Total_op_type l s _) = (if null l then empty
					   else space 
					        <> crossT printText0 ga l 
				                <+> text funS)
				           <> space <> printText0 ga s
    printText0 ga (Partial_op_type l s _) = (if null l then text quMark 
					     else space 
                                                  <> crossT printText0 ga l 
					          <+> text (funS ++ quMark))
					    <+> printText0 ga s

instance PrettyPrint OP_HEAD where
    printText0 ga (Total_op_head l s _) = 
	(if null l then empty 
	 else parens(semiT printText0 ga l))
	<> colon
	<+> printText0 ga s
    printText0 ga (Partial_op_head l s _) = 
	(if null l then empty 
	 else parens(semiT printText0 ga l))
	<> text (colonS ++ quMark)
        <+> printText0 ga s

instance PrettyPrint ARG_DECL where
    printText0 ga (Arg_decl l s _) = commaT printText0 ga l 
			      <+> colon
			      <> printText0 ga s

instance PrettyPrint OP_ATTR where
    printText0 _ (Assoc_op_attr) = text assocS
    printText0 _ (Comm_op_attr) = text commS 
    printText0 _ (Idem_op_attr) = text idemS
    printText0 ga (Unit_op_attr t) = text unitS <+> printText0 ga t

instance PrettyPrint PRED_ITEM where
    printText0 ga (Pred_decl l t _) = commaT printText0 ga l 
				  <+> (colon
				       <+> printText0 ga t)
    printText0 ga (Pred_defn n h f _) = printText0 ga n 
				        <> printText0 ga h
                                        <+> text equivS
				        <+> printText0 ga f

instance PrettyPrint PRED_TYPE where
    printText0 _ (Pred_type [] _) = parens (empty)
    printText0 ga (Pred_type l _) = crossT printText0 ga l

instance PrettyPrint PRED_HEAD where
    printText0 ga (Pred_head l _) = parens (semiT printText0 ga l)

instance PrettyPrint DATATYPE_DECL where
    printText0 ga (Datatype_decl s a _) = 
	printText0 ga s <+> 
	sep ((hang (text defnS) 4 (printText0 ga $ head a)):
	     (map (\x -> nest 2 $ ptext barS <+> nest 2 (printText0 ga x)) $ 
		  tail a))



instance PrettyPrint ALTERNATIVE where
    printText0 ga (Total_construct n l _) = printText0 ga n 
				 <> if null l then empty 
				    else parens(semiT printText0 ga l)
    printText0 ga (Partial_construct n l _) = printText0 ga n 
				 <> parens(semiT printText0 ga l)
				 <> text quMark
    printText0 ga (Subsorts l _) = text sortS <+> commaT printText0 ga l 

instance PrettyPrint COMPONENTS where
    printText0 ga (Total_select l s _) = commaT printText0 ga l 
				<> colon 
				<> printText0 ga s 
    printText0 ga (Partial_select l s _) = commaT printText0 ga l 
				<> text (colonS ++ quMark) 
				<> printText0 ga s 
    printText0 ga (Sort s) = printText0 ga s 	  

instance PrettyPrint VAR_DECL where
    printText0 ga (Var_decl l s _) = commaT printText0 ga l 
				<> colon 
				<> printText0 ga s 

instance PrettyPrint FORMULA where
    printText0 ga (Quantification q l f _) = 
	hang (printText0 ga q <+> semiT printText0 ga l) 4 $ 
	     char '.' <+> printText0 ga f
    printText0 ga (Conjunction l _) = 
	sep $ prepPunctuate (ptext lAnd <> space) $ 
	    map (condParensXjunction printText0 ga) l
    printText0 ga (Disjunction  l _) = 
	sep $ prepPunctuate (ptext lOr <> space) $ 
	    map (condParensXjunction printText0 ga) l
    printText0 ga i@(Implication f g _) = 
	hang (condParensImplEquiv printText0 ga i f <+> ptext implS) 4 $ 
	     condParensImplEquiv printText0 ga i g
    printText0 ga e@(Equivalence  f g _) = 
	hang (condParensImplEquiv printText0 ga e f <+> ptext equivS) 4 $
	     condParensImplEquiv printText0 ga e g
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
	     print_prefix_appl printText0 ga p' l
	   else condPrint_Mixfix printText0 ga p_id l
    printText0 ga (Definedness f _) = text defS <+> printText0 ga f
    printText0 ga (Existl_equation f g _) = 
	hang (printText0 ga f <+> ptext exEqual) 4 $ printText0 ga g
    printText0 ga (Strong_equation f g _) = 
	hang (printText0 ga f <+> ptext equalS) 4 $ printText0 ga g 
    printText0 ga (Membership f g _) = 
	printText0 ga f <+> ptext inS <+> printText0 ga g
    printText0 ga (Mixfix_formula t) = printText0 ga t
    printText0 _ (Unparsed_formula s _) = text s 

instance PrettyPrint QUANTIFIER where
    printText0 _ (Universal) = ptext forallS
    printText0 _ (Existential) = ptext existsS
    printText0 _ (Unique_existential) = ptext (existsS ++ exMark)

instance PrettyPrint PRED_SYMB where
    printText0 ga (Pred_name n) = printText0 ga n
    printText0 ga (Qual_pred_name n t _) = 
	parens $ ptext predS <+> printText0 ga n <+> colon <+> printText0 ga t
				       
instance PrettyPrint TERM where
    printText0 ga (Simple_id i) = printText0 ga i
    printText0 ga (Qual_var n t _) = 
	parens $ text varS <+> printText0 ga n <+> colon <+> printText0 ga t
    printText0 ga (Application o l _) = 
    {- TODO: consider string-, number-, list- and floating-annotations -}
	let (o_id,isQual) = 
		case o of
		       Op_name i          -> (i,False)
		       Qual_op_name i _ _ -> (i,True)
	    o' = printText0 ga o
	in if isQual then 
	     print_prefix_appl printText0 ga o' l
	   else 
	     if isLiteral (literal_map ga) o_id then
	       print_Literal printText0 ga o_id l
	     else
	       condPrint_Mixfix printText0 ga o_id l
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
    printText0 ga (Mixfix_parenthesized l _) = parens (commaT printText0 ga l)
    printText0 ga (Mixfix_bracketed l _) =   brackets (commaT printText0 ga l)
    printText0 ga (Mixfix_braced l _) =        braces (commaT printText0 ga l)

instance PrettyPrint OP_SYMB where
    printText0 ga (Op_name o) = printText0 ga o
    printText0 ga (Qual_op_name o t _) = parens(text opS
						<+> printText0 ga o
						<+> (colon
						     <> printText0 ga t))

----------------------------------------------------------------------------
----------------------------------------------------------------------------

{- old stuff or new stuff who knows / cares
----------
instance PrettyPrint SYMB_ITEMS where
    printText0 ga (Symb_items aa ab _) =
	let aa' = printText0 ga aa
	    ab' = fcat $ punctuate (comma<>space) $ map (printText0 ga) ab
	in aa' <+> ab'

instance PrettyPrint SYMB_MAP_ITEMS where
    printText0 ga (Symb_map_items aa ab _) =
	let aa' = printText0 ga aa
	    ab' = fcat $ punctuate (comma<>space) $ map (printText0 ga) ab
	in aa' <+> ab'

instance PrettyPrint SYMB_KIND where
    printText0 ga Implicit =
	empty
    printText0 ga Sorts_kind =
	ptext "sort"
    printText0 ga Ops_kind =
	ptext "op"
    printText0 ga Preds_kind =
	ptext "pred"

instance PrettyPrint SYMB where
    printText0 ga (Symb_id aa) =
	printText0 ga aa
    printText0 ga (Qual_id aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' <> colon <+> ab'

instance PrettyPrint TYPE where
    printText0 ga (O_type aa) =
	printText0 ga aa
    printText0 ga (P_type aa) =
	printText0 ga aa

instance PrettyPrint SYMB_OR_MAP where
    printText0 ga (Symb aa) =
	printText0 ga aa
    printText0 ga (Symb_map aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' <+> ptext "|->" <+> ab'

-}

instance PrettyPrint SYMB_ITEMS where
 printText0 ga (Symb_items k l _) = 
     printText0 ga k <> pluralS' <+> commaT printText0 ga l
     where pluralS' = case k of
			     Implicit -> empty
			     _        -> if length l > 1 then ptext "s" 
					 else empty

instance PrettyPrint SYMB_ITEMS_LIST where
    printText0 ga (Symb_items_list l _) = commaT printText0 ga l

instance PrettyPrint SYMB_MAP_ITEMS where
 printText0 ga (Symb_map_items k l _) = 
     printText0 ga k <> pluralS' <+> commaT printText0 ga l
     where pluralS' = case k of
			     Implicit -> empty
			     _        -> if length l > 1 then ptext "s" 
					 else empty

instance PrettyPrint SYMB_MAP_ITEMS_LIST where 
    printText0 ga (Symb_map_items_list l _) = commaT printText0 ga l

instance PrettyPrint SYMB_KIND where 
    printText0 _ Implicit = empty
    printText0 _ Sorts_kind = ptext sortS
    printText0 _ Ops_kind = ptext opS
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

condPrint_Mixfix :: (forall a .PrettyPrint a => GlobalAnnos -> a -> Doc) ->  
		    GlobalAnnos -> Id -> [TERM] -> Doc
condPrint_Mixfix pf ga i l =
    if isMixfix i then
       if length (filter isPlace tops) == length l then
	  print_mixfix_appl pf ga i l
       else 
          print_prefix_appl pf ga o' l
    else print_prefix_appl pf ga o' l
    where tops = case i of Id tp _ _ -> tp 
	  o' = pf ga i

-- printing consistent prefix application and predication
print_prefix_appl :: (forall a .PrettyPrint a => GlobalAnnos -> a -> Doc) ->  
		     GlobalAnnos -> Doc -> [TERM] -> Doc 
{- TODO: consider string-, number-, list- and floating-annotations -}
print_prefix_appl pf ga po' l = po' <> 
			     (if null l then empty 
			      else parens (commaT pf ga l))

print_Literal :: (forall a .PrettyPrint a => GlobalAnnos -> a -> Doc) ->  
		      GlobalAnnos -> Id -> [TERM] -> Doc
print_Literal pf ga li ts 
    | all (isSimple li) ts = case getLiteralType lmap li of
			     _ -> condPrint_Mixfix pf ga li ts
    | otherwise = condPrint_Mixfix pf ga li ts
    where isSimple i t = case t of
			 Application o its _ 
			     | oi == i   -> all (isSimple i) its
			     | otherwise -> False
			     where oi = 
				     case o of 
				     Qual_op_name _ _ _ -> 
					 error "cannot lierally Print Qual_id" 
				     Op_name x -> x
			 Simple_id _ -> True
			 _           -> False
	  lmap = literal_map ga

-- printing consitent mixfix application or predication
{- TODO: consider string-, number-, list- and floating-annotations -}
print_mixfix_appl :: (forall a .PrettyPrint a => GlobalAnnos -> a -> Doc) ->  
	       GlobalAnnos -> Id -> [TERM] -> Doc
print_mixfix_appl pf ga oid l = ft <+> fsep nlI <+> c <+> fsep nlT <+> lt
    where (tops,cs) = case oid of Id x1 x2 _ -> (x1,x2)
	  c = if null cs then empty 
	      else fsep $ map (sp_brackets . (pf ga)) cs
          (topsI,topsT) = splitMixToken tops
	  lI = take (length $ filter isPlace topsI) l
	  lT = drop (length $ filter isPlace topsI) l
	  nlI = fillIn topsI' lI'
	  nlT = fillIn topsT' lT'
	  isL3 = length tops >= 3
	  (topsI',lI',ft) = if isL3 && (isPlace $ head topsI) then
			      (tail topsI,tail lI,
			       condParensAppl pf ga oid (head lI) (Just ALeft))
			    else
			      (topsI,lI,empty)
	  (topsT',lT',lt) = if isL3 && 
			       (not $ null topsT) && 
                               (isPlace $ last topsT) 
			    then
			      (init topsT,init lT,
			       condParensAppl pf ga 
			                      oid (last lT) (Just ARight))
			    else
			      (topsT,lT,empty)
	  fillIn tps ts = let (_,nl) = mapAccumL pr ts tps in nl
	  pr [] top = ([], ptext $ showTok top "")
	  pr tS@(t:ts) top | isPlace top = (ts,
					    condParensAppl pf ga oid t Nothing)
			   | otherwise   = (tS,ptext $ showTok top "")

condParensAppl :: (GlobalAnnos -> TERM -> Doc) -> 
		  GlobalAnnos -> 
		  Id -> 
		  TERM -> 
		  Maybe AssocEither -> 
		  Doc
condParensAppl pf ga o_i t mdir = 
    case t of
    Simple_id _ -> t'
    Application _ [] _ -> t'
    Application o _ _ 
        -- ordinary appl (no place)
	| isOrdAppl i_i -> ptext "%[Ord_Appl]%" <+> t' 
	-- postfix appl
	| isOrdAppl o_i && isPostfix i_i -> ptext "%[OrdWithPost]%" <+> t' 
	| isMixfix  o_i && isPostfix i_i -> ptext "%[MixWithPost]%" <+> t' 
	-- prefix appl w/o parens
	| isOrdAppl o_i && isPrefix i_i  -> ptext "%[OrdWithPre]%" <+> t'
	| isPostfix o_i && isPrefix i_i  -> parens t'
	-- infix appl (left and right arg/place)
	| isInfix i_i && o_i == i_i -> ptext "%[Infix]%" <+>
	    case mdir of
		      Nothing -> condParensPrec ga o_i i_i t' 
		      Just ALeft | isLAssoc amap o_i -> t'
				 | otherwise -> parens t'
		      Just ARight | isRAssoc amap o_i -> t'
				  | otherwise -> parens t'
	| otherwise -> condParensPrec ga o_i i_i t'
	where i_i = case o of
			  Op_name i          -> i
			  Qual_op_name i _ _ -> i
	      amap = assoc_annos ga
    
    _ -> parens t'
    where t' = pf ga t


condParensPrec :: GlobalAnnos -> Id -> Id -> Doc -> Doc
condParensPrec ga o_i i_i t = parens t -- TODO


condParensImplEquiv :: (GlobalAnnos -> FORMULA -> Doc) -> 
		       GlobalAnnos -> FORMULA -> FORMULA -> Doc
condParensImplEquiv pf ga e_i f =  
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
				   _           -> parens f'
    Equivalence _ _ _ -> case f of Disjunction _ _ -> f'
				   Conjunction _ _ -> f'
				   Negation _ _ -> f' 
				   True_atom _  -> f' 
				   False_atom _ -> f'
				   Predication _ _ _ -> f'
				   Quantification _ _ _ _ -> f'
				   Existl_equation _ _ _ -> f'
				   Strong_equation _ _ _ -> f'
				   _           -> parens f'
    _ ->  error "Wrong call: condParensImplEquiv"
    where f' = pf ga f
condParensXjunction :: (GlobalAnnos -> FORMULA -> Doc) -> 
		       GlobalAnnos -> FORMULA -> Doc
condParensXjunction pf ga x = 
    case x of Negation _ _ -> x' 
	      True_atom _  -> x' 
	      False_atom _ -> x'
	      Predication _ _ _ -> x'
	      Existl_equation _ _ _ -> x'
	      Strong_equation _ _ _ -> x'
	      _            -> parens x' 
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