{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 
   
   latex output of the abstract syntax
-}

module HasCASL.LaTeX_HasCASL where

import HasCASL.As
import HasCASL.PrintAs
import HasCASL.Le
import HasCASL.Symbol
import HasCASL.PrintLe
import HasCASL.Morphism
import Common.Keywords
import HasCASL.HToken
import Common.Lib.Pretty
import qualified Common.Lib.Map as Map
import Common.Id
import Common.PPUtils
import Common.PrettyPrint
import Common.PrintLaTeX
import Common.GlobalAnnotations(GlobalAnnos)
import Common.LaTeX_AS_Annotation

instance PrintLaTeX Variance where 
    printLatex0 _ CoVar = text plusS
    printLatex0 _ ContraVar = text minusS
    printLatex0 _ InVar = empty

instance PrintLaTeX Kind where
    printLatex0 _ (Universe _) = text "Type"
    printLatex0 _ MissingKind = space
    printLatex0 ga (ClassKind ci _) = printLatex0 ga ci
    printLatex0 ga (Downset mt t _ _) =
	let tok = case mt of 
		  Nothing -> text "_" 
		  Just x -> text (tokStr x) <+> text dotS <+> text (tokStr x)
	    in braces (tok <+>
		       text lessS <+> printLatex0 ga t)
    printLatex0 ga (Intersection ks _) = printLList ga ks
    printLatex0 ga (FunKind k1 k2 _) = 
			  (case k1 of 
				  ExtKind (FunKind _ _ _) InVar _ -> parens
				  FunKind _ _ _ -> parens
				  _ -> id) (printLatex0 ga k1)
			  <+> text funS 
			  <+> printLatex0 ga k2
    printLatex0 ga (ExtKind k v _) = 
	(case v of
	       InVar -> id 
	       _ -> case k of
		    FunKind _ _ _ -> parens
		    _ -> id) (printLatex0 ga k) <> printLatex0 ga v

instance PrintLaTeX TypePattern where 
    printLatex0 ga (TypePattern name args _) = printLatex0 ga name
				 <> fcat (map (parens . printLatex0 ga) args)
    printLatex0 ga (TypePatternToken t) = printLatex0 ga t
    printLatex0 ga (MixfixTypePattern ts) = fsep (map (printLatex0 ga) ts)
    printLatex0 ga (BracketTypePattern k l _) = bracket k $ commaT_text ga l
    printLatex0 ga (TypePatternArg t _) = parens $ printLatex0 ga t

-- | print a 'Kind' plus a preceding colon (or nothing for 'star')
printLKind :: GlobalAnnos -> Kind -> Doc
printLKind ga kind = case kind of 
		    Universe _ -> empty
		    Downset Nothing t _ _ -> 
			space <> text lessS <+> printLatex0 ga t
		    _ -> space <> colon <+> printLatex0 ga kind

instance PrintLaTeX Type where 
    printLatex0 ga (TypeName name _k _i) = printLatex0 ga name 
    printLatex0 ga (TypeAppl t1 t2) = 
        case t1 of 
	TypeName (Id [a, Token "__" _, b] [] []) _ _ ->
	    printLatex0 ga a <> printLatex0 ga t2 <> printLatex0 ga b
	TypeAppl (TypeName (Id [Token "__" _, inTok, Token "__" _] 
			    [] []) _ _) t0 -> printLatex0 ga t0 
		     <+> printLatex0 ga inTok <+> printLatex0 ga t2
	_ -> (case t1 of 
		TypeName _ _ _ -> id
	        TypeToken _ -> id
		BracketType _ _ _ -> id
	        TypeAppl _ _ -> id 
		_ -> parens) (printLatex0 ga t1) <+> 
	     (case t2 of 
		TypeName _ _ _ -> id
	        TypeToken _ -> id
		BracketType _ _ _ -> id
		_ -> parens) (printLatex0 ga t2) 
    printLatex0 ga (TypeToken t) = printLatex0 ga t
    printLatex0 ga (BracketType k l _) = bracket k $ commaT_text ga l
    printLatex0 ga (KindedType t kind _) = (case t of 
					    FunType _ _ _ _ -> parens
					    ProductType [] _ -> id
					    ProductType _ _ -> parens
					    LazyType _ _ -> parens
					    TypeAppl _ _ -> parens
					    _ -> id) (printLatex0 ga t) 
					  <+> colon <+> printLatex0 ga kind
    printLatex0 ga (MixfixType ts) = fsep (map (printLatex0 ga) ts)
    printLatex0 ga (LazyType t _) = text quMark <+> (case t of 
					    FunType _ _ _ _ -> parens
					    ProductType [] _ -> id
					    ProductType _ _ -> parens
					    KindedType _ _ _ -> parens
					    _ -> id) (printLatex0 ga t)  
    printLatex0 ga (ProductType ts _) = if null ts then ptext "Unit"
				       -- parens empty 
			  else fsep (punctuate (space <> text timesS) 
				     (map ( \ t -> 
					    (case t of 
					    FunType _ _ _ _ -> parens
					    ProductType [] _ -> id
					    ProductType _ _ -> parens
					    _ -> id) $ printLatex0 ga t) ts))
    printLatex0 ga (FunType t1 arr t2 _) = (case t1 of 
					   FunType _ _ _ _ -> parens
					   _ -> id) (printLatex0 ga t1)
				      <+> printLatex0 ga arr
				      <+> printLatex0 ga t2

instance PrintLaTeX Pred where
    printLatex0 ga (IsIn c ts) = if null ts then printLatex0 ga c 
				else if null $ tail ts then
				     printLatex0 ga (head ts) <+>
				     colon <+> printLatex0 ga c
				else printLatex0 ga c <+>
				     fsep (punctuate space
				     (map (printLatex0 ga) ts))
				     
instance PrintLaTeX t => PrintLaTeX (Qual t) where
    printLatex0 ga (ps :=> t) = (if null ps then empty
			       else parens $ commaT_text ga ps <+>
				    ptext implS <+> space) <>
					       printLatex0 ga t

-- no curried notation for bound variables 
instance PrintLaTeX TypeScheme where
    printLatex0 ga (TypeScheme vs t _) = noPrint (null vs) (text forallS
						    <+> semiT_text ga vs 
						    <+> text dotS <+> space)
					 <> printLatex0 ga t

instance PrintLaTeX Partiality where
    printLatex0 _ Partial = text quMark
    printLatex0 _ Total = text exMark

instance PrintLaTeX Arrow where 
    printLatex0 _ a = text $ show a

instance PrintLaTeX Quantifier where 
    printLatex0 _ Universal = text forallS
    printLatex0 _ Existential = text existsS 
    printLatex0 _ Unique = text $ existsS ++ exMark

instance PrintLaTeX TypeQual where 
    printLatex0 _ OfType = colon
    printLatex0 _ AsType = text asS
    printLatex0 _ InType = text inS

instance PrintLaTeX Term where
    printLatex0 ga (QualVar v t _) = parens $ text varS
			<+> printLatex0 ga v
			<+> colon
			<+> printLatex0 ga t
    printLatex0 ga (QualOp b n t _) = parens $
			printLatex0 ga b
			<+> printLatex0 ga n
			<+> colon
			<+> printLatex0 ga t
    printLatex0 ga (ResolvedMixTerm n ts _) = (if isSimpleId n then
					     id else parens) (printLatex0 ga n)
			<> noPrint (null ts) (parens $ commaT_text ga ts)
    printLatex0 ga (ApplTerm t1 t2 _) = printLatex0 ga t1
			<+> (case t2 of 
			     QualVar _ _ _ -> id 
			     QualOp _ _ _ _ -> id 
			     TupleTerm _ _ -> id
			     BracketTerm Parens _ _ -> id
			     ResolvedMixTerm _ [] _ -> id
			     TermToken _ -> id
			     _ -> parens) (printLatex0 ga t2)
    printLatex0 ga (TupleTerm ts _) = parens $ commaT_text ga ts 
    printLatex0 ga (TypedTerm term q typ _) = printLatex0 ga term
			  <+> printLatex0 ga q
			  <+> printLatex0 ga typ
    printLatex0 ga (QuantifiedTerm q vs t _) = printLatex0 ga q
					  <+> semiT_text ga vs 
					  <+> text dotS    
					  <+> printLatex0 ga t
    printLatex0 ga (LambdaTerm ps q t _) = text lamS
				      <+> (case ps of
					   [p] -> printLatex0 ga p
					   _ -> fcat $ map 
					        (parens.printLatex0 ga) ps)
				      <+> (case q of 
					   Partial -> text dotS
					   Total -> text $ dotS ++ exMark)
				      <+> printLatex0 ga t
    printLatex0 ga (CaseTerm t es _ ) = text caseS
				   <+> printLatex0 ga t
				   <+> text ofS
				   <+> vcat (punctuate (text " | ")
					     (map (printLEq ga funS) es))
    printLatex0 ga (LetTerm b es t _) = 
	let dt = printLatex0 ga t
	    des = vcat $ punctuate semi $
		  map (printLEq ga equalS) es
        in case b of 
		  Let -> text letS <+> des <+> text inS <+> dt
		  Where -> dt <+> text whereS <+> des 
    printLatex0 ga (TermToken t) = printLatex0 ga t
    printLatex0 ga (MixInTerm t _) = text inS <+> printLatex0 ga t
    printLatex0 ga (MixfixTerm ts) = fsep $ map (printLatex0 ga) ts
    printLatex0 ga (BracketTerm k l _) = bracket k $ commaT_text ga l

instance PrintLaTeX Pattern where 
    printLatex0 ga (PatternVar v) = printLatex0 ga v
    printLatex0 ga (PatternConstr n t _) = printLatex0 ga n 
			  <+> colon
			  <+> printLatex0 ga t 
    printLatex0 ga (ResolvedMixPattern n args _) = 
	(if isSimpleId n then id else parens) (printLatex0 ga n) 
			     <> (case args of 
				 [] -> empty
				 [t@(TuplePattern _ _)] -> 
				           printLatex0 ga t
				 _ -> parens $ commaT_text ga args)
    printLatex0 ga (ApplPattern p1 p2 _) =  printLatex0 ga p1
			<+> (case p2 of 
			     TuplePattern _ _ -> id
			     BracketPattern Parens _ _ -> id
			     ResolvedMixPattern _ [] _ -> id
			     PatternToken _ -> id
			     _ -> parens) (printLatex0 ga p2)
    printLatex0 ga (TuplePattern ps _) = parens $ commaT_text ga ps
    printLatex0 ga (TypedPattern p t _) = printLatex0 ga p 
			  <+> colon
			  <+> printLatex0 ga t 
    printLatex0 ga (AsPattern v p _) = printLatex0 ga v
			  <+> text asP
			  <+> printLatex0 ga p
    printLatex0 ga (PatternToken t) = printLatex0 ga t
    printLatex0 ga (BracketPattern k l _) = bracket k $ commaT_text ga l
    printLatex0 ga (MixfixPattern ps) = fsep (map (printLatex0 ga) ps)

-- | print an equation with different symbols between 'Pattern' and 'Term'
printLEq :: GlobalAnnos -> String -> ProgEq -> Doc
printLEq ga s (ProgEq p t _) = fsep [printLatex0 ga p 
			  , text s
			  , printLatex0 ga t] 

instance PrintLaTeX VarDecl where 
    printLatex0 ga (VarDecl v t _ _) = printLatex0 ga v <+> colon
						 <+> printLatex0 ga t

instance PrintLaTeX GenVarDecl where 
    printLatex0 ga (GenVarDecl v) = printLatex0 ga v
    printLatex0 ga (GenTypeVarDecl tv) = printLatex0 ga tv

instance PrintLaTeX TypeArg where 
    printLatex0 ga (TypeArg v c _ _) = printLatex0 ga v <+> colon 
				      <+> printLatex0 ga c

-- | don't print an empty list and put parens around longer lists
printLList :: (PrintLaTeX a) => GlobalAnnos -> [a] -> Doc
printLList ga l =  case l of 
	   []  -> empty
	   [x] -> printLatex0 ga x
	   _   -> parens $ commaT_text ga l

instance PrintLaTeX InstOpId where
    printLatex0 ga (InstOpId n l _) = printLatex0 ga n 
				     <> noPrint (null l) 
					(brackets $ semiT_text ga l)

------------------------------------------------------------------------
-- item stuff
------------------------------------------------------------------------
-- | print a 'TypeScheme' as a pseudo type
printLPseudoType :: GlobalAnnos -> TypeScheme -> Doc
printLPseudoType ga (TypeScheme l t _) = noPrint (null l) (text lamS 
				<+> (if null $ tail l then
				     printLatex0 ga $ head l
				     else fcat(map (parens . printLatex0 ga) l))
				<+> text dotS <> space) <> printLatex0 ga t

instance PrintLaTeX BasicSpec where 
    printLatex0 ga (BasicSpec l) = vcat (map (printLatex0 ga) l)

instance PrintLaTeX ProgEq where
    printLatex0 ga = printLEq ga equalS

instance PrintLaTeX BasicItem where 
    printLatex0 ga (SigItems s) = printLatex0 ga s
    printLatex0 ga (ProgItems l _) = text programS <+> semiT_text ga l
    printLatex0 ga (ClassItems i l _) = text classS <+> printLatex0 ga i
			       <+> semiT_text ga l
    printLatex0 ga (GenVarItems l _) = text varS <+> semiT_text ga l
    printLatex0 ga (FreeDatatype l _) = text freeS <+> text typeS 
				    <+> semiT_text ga l
    printLatex0 ga (GenItems l _) = text generatedS <+> braces (semiT_text ga l)
    printLatex0 ga (AxiomItems vs fs _) = (if null vs then empty
			       else text forallS <+> semiT_text ga vs)
			       $$ vcat (map 
					 (\x -> text dotS <+> printLatex0 ga x) 
					 fs)
    printLatex0 ga (Internal l _) = text internalS <+> braces (semiT_text ga l)


instance PrintLaTeX OpBrand where
    printLatex0 _ b = text $ case b of 
				    Fun -> functS 
				    Op -> opS
				    Pred -> "predfun"

instance PrintLaTeX SigItems where 
    printLatex0 ga (TypeItems i l _) = text typeS <+> printLatex0 ga i 
				      <+> semiT_text ga l
    printLatex0 ga (OpItems b l _) = printLatex0 ga b <+> semiT_text ga l

instance PrintLaTeX Instance where
    printLatex0 _ Instance = text instanceS
    printLatex0 _ _ = empty
		      
instance PrintLaTeX ClassItem where 
    printLatex0 ga (ClassItem d l _) = printLatex0 ga d $$ 
				   if null l then empty 
				      else braces (semiT_text ga l)

instance PrintLaTeX ClassDecl where 
    printLatex0 ga (ClassDecl l k _) = commaT_text ga l 
				      <+> text lessS <+> printLatex0 ga k

instance PrintLaTeX Vars where
    printLatex0 ga (Var v) = printLatex0 ga v
    printLatex0 ga (VarTuple vs _) = parens $ commaT_text ga vs

instance PrintLaTeX TypeItem where 
    printLatex0 ga (TypeDecl l k _) = commaT_text ga l <> 
				  printLKind ga k
    printLatex0 ga (SubtypeDecl l t _) = commaT_text ga l <+> text lessS 
					<+> printLatex0 ga t
    printLatex0 ga (IsoDecl l _) = cat(punctuate (text " = ") 
				      (map (printLatex0 ga) l))
    printLatex0 ga (SubtypeDefn p v t f _) = printLatex0 ga p
			       <+> text equalS 
			       <+> braces (printLatex0 ga v 
					   <+> colon
					   <+> printLatex0 ga t 
					   <+> text dotS
					   <+> printLatex0 ga f)
    printLatex0 ga (AliasType p k t _) =  (printLatex0 ga p <>
					  case k of 
					  Nothing -> empty
					  Just j -> space <> colon <+> 
					           printLatex0 ga j)
				       <+> text assignS
				       <+> printLPseudoType ga t
    printLatex0 ga (Datatype t) = printLatex0 ga t

instance PrintLaTeX OpItem where 
    printLatex0 ga (OpDecl l t as _) = commaT_text ga l <+> colon
				   <+> (printLatex0 ga t
					<> (if null as then empty else comma)
					<> commaT_text ga as)
    printLatex0 ga (OpDefn n ps s p t _) = 
	(printLatex0 ga n <> fcat (map (parens . semiT_text ga) ps))
			    <+> (colon <> if p == Partial 
				 then text quMark else empty)
 			    <+> printLatex0 ga s 
			    <+> text equalS
			    <+> printLatex0 ga t

instance PrintLaTeX BinOpAttr where 
    printLatex0 _ Assoc = text assocS
    printLatex0 _ Comm = text commS
    printLatex0 _ Idem = text idemS

instance PrintLaTeX OpAttr where 
    printLatex0 ga (BinOpAttr a _) = printLatex0 ga a
    printLatex0 ga (UnitOpAttr t _) = text unitS <+> printLatex0 ga t

instance PrintLaTeX DatatypeDecl where 
    printLatex0 ga (DatatypeDecl p k as d _) = (printLatex0 ga p <>
					       printLKind ga k)
				  <+> text defnS
				  <+> vcat(punctuate (text " | ") 
					   (map (printLatex0 ga) as))
				  <+> case d of [] -> empty
						_ -> text derivingS
							  <+> commaT_text ga d

instance PrintLaTeX Alternative where 
    printLatex0 ga (Constructor n cs p _) = 
	printLatex0 ga n <+> fsep (map (parens . semiT_text ga) cs)
		       <+> (case p of {Partial -> text quMark;
				       _ -> empty})
    printLatex0 ga (Subtype l _) = text typeS <+> commaT_text ga l

instance PrintLaTeX Component where 
    printLatex0 ga (Selector n p t _ _) = printLatex0 ga n 
				<> colon <> (case p of { Partial ->text quMark;
							 _ -> empty } 
					      <+> printLatex0 ga t)
    printLatex0 ga (NoSelector t) = printLatex0 ga t

instance PrintLaTeX OpId where 
    printLatex0 ga (OpId n ts _) = printLatex0 ga n 
				  <+> noPrint (null ts) 
				      (brackets $ commaT_text ga ts)

instance PrintLaTeX ClassInfo where
    printLatex0 ga (ClassInfo ks) =
	   space <> ptext lessS <+> printLList ga ks

instance PrintLaTeX TypeDefn where
    printLatex0 _ NoTypeDefn = empty
    printLatex0 _ PreDatatype = space <> ptext "%(data type)%"
    printLatex0 _ TypeVarDefn = space <> ptext "%(var)%"
    printLatex0 ga (AliasTypeDefn s) = space <> ptext assignS 
				      <+> printLPseudoType ga s
    printLatex0 ga (Supertype v t f) = space <> ptext equalS <+> 
					 braces (printLatex0 ga v 
					   <+> colon
					   <+> printLatex0 ga t 
					   <+> text dotS
					   <+> printLatex0 ga f)
    printLatex0 ga (DatatypeDefn k args alts)  = ptext " %[" <>
	let om = ptext typeS <+> ptext place <+> printLList ga args 
		 <+> ptext defnS $$ 
		 vcat (map (printLatex0 ga) alts)
	    in (case k of
		Loose -> empty
		Free -> ptext freeS <> space
		Generated -> ptext generatedS <> space) <> om <> ptext "]%"

instance PrintLaTeX AltDefn where
    printLatex0 ga (Construct i ts p sels) = 
	printLatex0 ga i <+> colon 
	<+> listSep_text (space<>ptext funS<>space) ga ts <+>
	    ptext (case p of 
		   Partial -> funS ++ quMark
		   Total -> funS) <+> ptext place 
	<+> hcat (map (parens . printLatex0 ga) sels) 

instance PrintLaTeX Selector where
    printLatex0 ga (Select i t p) = 
	printLatex0 ga i <+> (case p of 
			     Partial -> ptext ":?"
			     Total -> colon) <+> printLatex0 ga t

instance PrintLaTeX TypeInfo where
    printLatex0 ga (TypeInfo _ ks sups defn) =
	space <> colon <+> printLList ga ks
	<> noPrint (null sups)
	   (space <> ptext lessS <+> printLList ga sups)
        <> printLatex0 ga defn

instance PrintLaTeX ConstrInfo where
    printLatex0 ga (ConstrInfo i t) = 
	printLatex0 ga i <+> colon <+> printLatex0 ga t

instance PrintLaTeX OpDefn where
    printLatex0 _ (NoOpDefn b) = space <> ptext ("%(" ++ show b ++ ")%")
    printLatex0 _ VarDefn = space <> ptext "%(var)%"
    printLatex0 _ (ConstructData i) = space <> ptext ("%(construct " ++
				     showId i ")%")
    printLatex0 ga (SelectData c i) = space <> ptext ("%(select from " ++
				     showId i " constructed by")
				    $$ printLList ga c <> ptext ")%"
    printLatex0 ga (Definition b t) = printLatex0 ga (NoOpDefn b) <+> 
				     ptext equalS <+> printLatex0 ga t
 
instance PrintLaTeX OpInfo where
    printLatex0 ga o = space <> colon <+> printLatex0 ga (opType o)
		      <> (case opAttrs o of 
			  [] -> empty 
			  l -> comma <> commaT_text ga l)
		      <>  printLatex0 ga (opDefn o)
 
instance PrintLaTeX OpInfos where
    printLatex0 ga (OpInfos l) = vcat $ map (printLatex0 ga) l

instance PrintLaTeX a => PrintLaTeX (Maybe a) where
    printLatex0 _ Nothing = empty
    printLatex0 ga (Just c) =  printLatex0 ga c

instance PrintLaTeX Env where
    printLatex0 ga (Env{classMap=cm, typeMap=tm, 
		       assumps=as, sentences=se, envDiags=ds}) = 
	noPrint (Map.isEmpty cm) (header "Classes")
	$$ printMap0 ga cm
	$$ noPrint (Map.isEmpty tm) (header "Type Constructors")
	$$ printMap0 ga tm
	$$ noPrint (Map.isEmpty as) (header "Assumptions")
        $$ printMap0 ga as
	$$ noPrint (null se) (header "Sentences")
        $$ vcat (map (printLatex0 ga) se)
	$$ noPrint (null ds) (header "Diagnostics")
	$$ vcat (map (printText0 ga) $ reverse ds)
	where header s =  ptext "%%" <+> ptext s 
			  <+> ptext (replicate (70 - length s) '-')
	      printMap0 :: (PrintLaTeX a, Ord a, PrintLaTeX b)  
			   => GlobalAnnos -> Map.Map a b -> Doc
	      printMap0 g m =
		  let l = Map.toList m in
			  vcat(map (\ (a, b) -> printLatex0 g a 
				    <> printLatex0 g b) l)

instance PrintLaTeX SymbolType where
    printLatex0 ga t = case t of 
      OpAsItemType (TySc sc) -> printLatex0 ga sc
      TypeAsItemType k -> printLatex0 ga k
      ClassAsItemType k -> printLatex0 ga k

instance PrintLaTeX Morphism where
  printLatex0 ga m = braces (printLatex0 ga (msource m)) 
		    $$ text mapsTo
		    <+> braces (printLatex0 ga (mtarget m))

instance PrintLaTeX Symbol where
  printLatex0 ga s = text (case symbType s of 
			  OpAsItemType _ -> opS
			  TypeAsItemType _ -> typeS
			  ClassAsItemType _ -> classS) <+> 
                    printLatex0 ga (symName s) <+> text colonS <+> 
		    printLatex0 ga (symbType s)

instance PrintLaTeX RawSymbol where
  printLatex0 ga rs = case rs of
      ASymbol s -> printLatex0 ga s
      AnID i -> printLatex0 ga i
      AKindedId k i -> text (case k of 
           SK_type -> typeS
           SK_op -> opS 
           SK_class -> classS
	   _ -> "") <+> printLatex0 ga i

instance PrintLaTeX Symb where
    printLatex0 ga (Symb i mt _) =
	printLatex0 ga i <> (case mt of Nothing -> empty
			                Just (SymbType t) -> 
					  empty <+> colon <+>
					    printLatex0 ga t)

instance PrintLaTeX SymbItems where
    printLatex0 ga (SymbItems k syms _ _) =
	printSK k <> commaT_text ga syms

instance PrintLaTeX SymbOrMap where
    printLatex0 ga (SymbOrMap s mt _) =
	printLatex0 ga s <> (case mt of Nothing -> empty
			                Just t -> 
					  empty <+> ptext mapsTo <+>
					    printLatex0 ga t)

instance PrintLaTeX SymbMapItems where
    printLatex0 ga (SymbMapItems k syms _ _) =
	printSK k <> commaT_text ga syms



	
