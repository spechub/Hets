{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 
   
   printing data types of the abstract syntax
-}

module HasCASL.PrintAs where

import HasCASL.As
import Common.Keywords
import HasCASL.HToken
import Common.Lib.Pretty
import Common.Id
import Common.PPUtils
import Common.PrettyPrint
import Common.GlobalAnnotations(GlobalAnnos)
import Common.AS_Annotation(mapAnM)

-- | short cut for: if b then empty else d
noPrint :: Bool -> Doc -> Doc
noPrint b d = if b then empty else d

instance PrettyPrint Variance where 
    printText0 _ v = text $ show v

instance PrettyPrint Kind where
    printText0 ga knd = case knd of
        Intersection [] _ -> text "Type"
        MissingKind -> space
        ClassKind ci _ -> printText0 ga ci
        Downset mt t _ _ -> 
	    let tok = case mt of 
		    Nothing -> text "_" 
		    Just x -> text (tokStr x) <+> text dotS <+> text (tokStr x)
	    in braces (tok <+>
		       text lessS <+> printText0 ga t)
        Intersection ks _ -> printList0 ga ks
        FunKind k1 k2 _ -> 
			  (case k1 of 
				  FunKind _ _ _ -> parens
				  _ -> id) (printText0 ga k1)
			  <+> text funS 
			  <+> printText0 ga k2
        ExtKind k v _ -> (case k of
		    FunKind _ _ _ -> parens
		    _ -> id) (printText0 ga k) <> printText0 ga v

instance PrettyPrint TypePattern where 
    printText0 ga tp = case tp of
        TypePattern name args _ -> printText0 ga name
				 <> fcat (map (parens . printText0 ga) args)
        TypePatternToken t -> printText0 ga t
        MixfixTypePattern ts -> fsep (map (printText0 ga) ts)
        BracketTypePattern k l _ -> bracket k $ commaT_text ga l
        TypePatternArg t _ -> parens $ printText0 ga t

-- | put proper brackets around a document
bracket :: BracketKind -> Doc -> Doc
bracket b t = let (o,c) = getBrackets b in ptext o <> t <> ptext c

-- | print a 'Kind' plus a preceding colon (or nothing for 'star')
printKind :: GlobalAnnos -> Kind -> Doc
printKind ga kind = case kind of 
		    Intersection [] _ -> empty
		    Downset Nothing t _ _ -> 
			space <> text lessS <+> printText0 ga t
		    _ -> space <> colon <+> printText0 ga kind

instance PrettyPrint Type where 
    printText0 ga ty = case ty of
        TypeName name _k _i -> printText0 ga name 
        TypeAppl t1 t2 -> case t1 of 
	    TypeName (Id [a, Token "__" _, b] [] []) _ _ ->
	        printText0 ga a <> printText0 ga t2 <> printText0 ga b
	    TypeAppl (TypeName (Id [Token "__" _, inTok, Token "__" _] 
				[] []) _ _) t0 -> printText0 ga t0 
			 <+> printText0 ga inTok <+> printText0 ga t2
	    _ -> (case t1 of 
		  TypeName _ _ _ -> id
	          TypeToken _ -> id
		  BracketType _ _ _ -> id
	          TypeAppl _ _ -> id 
		  _ -> parens) (printText0 ga t1) <+> 
		 (case t2 of 
		  TypeName _ _ _ -> id
	          TypeToken _ -> id
		  BracketType _ _ _ -> id
		  _ -> parens) (printText0 ga t2) 
	ExpandedType t1 _ -> printText0 ga t1
        TypeToken t -> printText0 ga t
        BracketType k l _ -> bracket k $ commaT_text ga l
        KindedType t kind _ -> (case t of 
				FunType _ _ _ _ -> parens
				ProductType [] _ -> id
				ProductType _ _ -> parens
				LazyType _ _ -> parens
				TypeAppl _ _ -> parens
				_ -> id) (printText0 ga t) 
				       <+> colon <+> printText0 ga kind
        MixfixType ts -> fsep (map (printText0 ga) ts)
        LazyType t _ -> text quMark <+> (case t of 
					 FunType _ _ _ _ -> parens
					 ProductType [] _ -> id
					 ProductType _ _ -> parens
					 KindedType _ _ _ -> parens
					 _ -> id) (printText0 ga t)  
        ProductType ts _ -> if null ts then ptext "Unit"
				       -- parens empty 
			  else fsep (punctuate (space <> char '*') 
				     (map ( \ t -> 
					    (case t of 
					    FunType _ _ _ _ -> parens
					    ProductType [] _ -> id
					    ProductType _ _ -> parens
					    _ -> id) $ printText0 ga t) ts))
        FunType t1 arr t2 _ -> (case t1 of 
				FunType _ _ _ _ -> parens
				_ -> id) (printText0 ga t1)
					<+> printText0 ga arr
					<+> printText0 ga t2

instance PrettyPrint Pred where
    printText0 ga (IsIn c ts) = if null ts then printText0 ga c 
				else if null $ tail ts then
				     printText0 ga (head ts) <+>
				     colon <+> printText0 ga c
				else printText0 ga c <+>
				     fsep (punctuate space
				     (map (printText0 ga) ts))
				     
instance PrettyPrint t => PrettyPrint (Qual t) where
    printText0 ga (ps :=> t) = (if null ps then empty
			       else parens $ commaT_text ga ps <+>
				    ptext implS <+> space) <>
					       printText0 ga t

-- no curried notation for bound variables 
instance PrettyPrint TypeScheme where
    printText0 ga (TypeScheme vs t _) = let tdoc = printText0 ga t in 
	if null vs then tdoc else 
	   hang (text forallS <+> semiT_text ga vs <+> text dotS) 2 tdoc

instance PrettyPrint Instance where 
    printText0 _ i = case i of
        Instance -> space <> text instanceS
	Plain -> empty 

instance PrettyPrint Partiality where
    printText0 _ p = case p of
        Partial -> text quMark
	Total -> empty 

instance PrettyPrint Arrow where 
    printText0 _ a = text $ show a

instance PrettyPrint Quantifier where 
    printText0 _ q = text $ show q

instance PrettyPrint TypeQual where 
    printText0 _ q = text $ show q

instance PrettyPrint Term where
    printText0 ga t = printTerm ga 
	   (case t of 
		  QualVar _ -> True
		  QualOp _ _ _ _ -> True
		  _ -> False) t

unPredType :: Type -> Type
unPredType t = case t of
	       FunType ty PFunArr (ProductType [] _) _ -> ty
	       _ -> t

unPredTypeScheme :: TypeScheme -> TypeScheme
unPredTypeScheme = mapTypeOfScheme unPredType

printTerm :: GlobalAnnos -> Bool -> Term -> Doc
printTerm ga b trm = 
    let ppParen = if b then parens else id 
	commaT = fsep . punctuate comma . map (printTerm ga False)
    in
	(case trm of
	       TupleTerm _ _ -> id
	       BracketTerm _ _ _ -> id
	       TermToken _ -> id
	       MixTypeTerm _ _ _ -> id
               _ -> ppParen)
      $ case trm of
        QualVar vd -> text varS <+> printText0 ga vd
        QualOp br n t _ -> sep [printText0 ga br <+> printText0 ga n,
			        colon <+> printText0 ga 
				(if isPred br then unPredTypeScheme t else t)]
        ResolvedMixTerm n ts _ -> 
	    case ts of 
	    [] ->  printText0 ga n
	    [t] -> printText0 ga n <> printTerm ga True t
	    _ -> printText0 ga n <> 
		 parens (commaT ts)
        ApplTerm t1 t2 _ -> cat [printText0 ga t1, nest 2
			$ printTerm ga True t2]
        TupleTerm ts _ -> parens (commaT ts)
        TypedTerm term q typ _ -> hang (printText0 ga term
			  <+> printText0 ga q)
			  4 $ printText0 ga typ
        QuantifiedTerm q vs t _ -> hang (printText0 ga q
					  <+> semiT_text ga vs)
					  2 (text dotS    
					  <+> printText0 ga t)
        LambdaTerm ps q t _ -> hang (text lamS
				      <+> (case ps of
					   [p] -> printText0 ga p
					   _ -> fcat $ map 
					     (parens . printTerm ga False) ps))
				      2 ((case q of 
					   Partial -> text dotS
					   Total -> text $ dotS ++ exMark)
					 <+> printText0 ga t)
        CaseTerm t es _  -> hang (text caseS
				   <+> printText0 ga t
				   <+> text ofS)
				   4 $ vcat (punctuate (text " | ")
					     (map (printEq0 ga funS) es))
        LetTerm br es t _ -> 
	    let dt = printText0 ga t
	        des = vcat $ punctuate semi $
		      map (printEq0 ga equalS) es
		in case br of 
		Let -> sep [text letS <+> des, text inS <+> dt]
		Where -> hang (sep [dt, text whereS]) 6 des 
        TermToken t -> printText0 ga t
        MixTypeTerm q t _ -> printText0 ga q <+> printText0 ga t
        MixfixTerm ts -> fsep $ map (printText0 ga) ts
        BracketTerm k l _ -> bracket k $ commaT l
        AsPattern v p _ -> printText0 ga v
			  <+> text asP
			  <+> printText0 ga p

-- | print an equation with different symbols between 'Pattern' and 'Term'
printEq0 :: GlobalAnnos -> String -> ProgEq -> Doc
printEq0 ga s (ProgEq p t _) = hang (hang (printText0 ga p) 2 $ text s) 
			       4 $ printText0 ga t

instance PrettyPrint VarDecl where 
    printText0 ga (VarDecl v t _ _) = printText0 ga v <> 
       case t of 
       MixfixType [] -> empty 
       _ -> space <> colon <+> printText0 ga t

instance PrettyPrint GenVarDecl where 
    printText0 ga gvd = case gvd of 
        GenVarDecl v -> printText0 ga v
        GenTypeVarDecl tv -> printText0 ga tv

instance PrettyPrint TypeArg where 
    printText0 ga (TypeArg v c _ _) = printText0 ga v <+> colon 
				      <+> printText0 ga c

-- | don't print an empty list and put parens around longer lists
printList0 :: (PrettyPrint a) => GlobalAnnos -> [a] -> Doc
printList0 ga l =  case l of 
	   []  -> empty
	   [x] -> printText0 ga x
	   _   -> parens $ commaT_text ga l

instance PrettyPrint InstOpId where
    printText0 ga (InstOpId n l _) = printText0 ga n 
				     <> noPrint (null l) 
					(brackets $ semiT_text ga l)

------------------------------------------------------------------------
-- item stuff
------------------------------------------------------------------------
-- | print a 'TypeScheme' as a pseudo type
printPseudoType :: GlobalAnnos -> TypeScheme -> Doc
printPseudoType ga (TypeScheme l t _) = noPrint (null l) (text lamS 
				<+> (if null $ tail l then
				     printText0 ga $ head l
				     else fcat(map (parens . printText0 ga) l))
				<+> text dotS <> space) <> printText0 ga t

instance PrettyPrint BasicSpec where 
    printText0 ga (BasicSpec l) = vcat (map (printText0 ga) l)

instance PrettyPrint ProgEq where
    printText0 ga = printEq0 ga equalS

instance PrettyPrint BasicItem where 
    printText0 ga bi = case bi of
        SigItems s -> printText0 ga s
        ProgItems l _ -> text programS <+> semiT_text ga l
        ClassItems i l _ -> text classS <> printText0 ga i <+> semiT_text ga l
        GenVarItems l _ -> text varS <+> semiT_text ga l
        FreeDatatype l _ -> text freeS <+> text typeS 
				    <+> semiT_text ga l
        GenItems l _ -> text generatedS <+> braces (semiT_text ga l)
        AxiomItems vs fs _ -> (if null vs then empty
			       else text forallS <+> semiT_text ga vs)
			       $$ vcat (map 
					 (\x -> text dotS <+> printText0 ga x) 
					 fs)
        Internal l _ -> text internalS <+> braces (semiT_text ga l)


instance PrettyPrint OpBrand where
    printText0 _ b = text $ show b

instance PrettyPrint SigItems where 
    printText0 ga si = case si of
        TypeItems i l _ -> text typeS <> printText0 ga i <+> semiT_text ga l
        OpItems b l _ -> printText0 ga b <+> semiT_text ga 
			 (if isPred b then concat $ 
			  mapAnM ((:[]) . mapOpItem) l else l)

instance PrettyPrint ClassItem where 
    printText0 ga (ClassItem d l _) = printText0 ga d $$ 
				   if null l then empty 
				      else braces (semiT_text ga l)

instance PrettyPrint ClassDecl where 
    printText0 ga (ClassDecl l k _) = commaT_text ga l 
				      <+> text lessS <+> printText0 ga k

instance PrettyPrint Vars where
    printText0 ga vd = case vd of
        Var v -> printText0 ga v
        VarTuple vs _ -> parens $ commaT_text ga vs

instance PrettyPrint TypeItem where 
    printText0 ga ti = case ti of
        TypeDecl l k _ -> commaT_text ga l <> 
				  printKind ga k
        SubtypeDecl l t _ -> commaT_text ga l <+> text lessS 
					<+> printText0 ga t
        IsoDecl l _ -> cat(punctuate (text " = ") 
				      (map (printText0 ga) l))
        SubtypeDefn p v t f _ -> printText0 ga p
			       <+> text equalS 
			       <+> braces (printText0 ga v 
					   <+> colon
					   <+> printText0 ga t 
					   <+> text dotS
					   <+> printText0 ga f)
        AliasType p k t _ ->  (printText0 ga p <>
					  case k of 
					  Nothing -> empty
					  Just j -> space <> colon <+> 
					           printText0 ga j)
				       <+> text assignS
				       <+> printPseudoType ga t
        Datatype t -> printText0 ga t

mapOpItem :: OpItem -> OpItem
mapOpItem oi = case oi of
    OpDecl l t as ps -> OpDecl l (unPredTypeScheme t) as ps
    OpDefn n ps s p t qs -> OpDefn n ps (unPredTypeScheme s) p t qs

instance PrettyPrint OpItem where 
    printText0 ga oi = case oi of
        OpDecl l t as _ -> commaT_text ga l <+> colon
				   <+> (printText0 ga t
					<> (if null as then empty 
					    else comma <> space)
					<> commaT_text ga as)
        OpDefn n ps s p t _ -> hang
	    (hang (printText0 ga n <> fcat (map (parens . semiT_text ga) ps))
			    2 (colon <> printText0 ga p
 			    <+> printText0 ga s)) 
			    2 (text equalS
			       <+> printText0 ga t)

instance PrettyPrint BinOpAttr where 
    printText0 _ a = text $ case a of
        Assoc -> assocS
        Comm -> commS
        Idem -> idemS

instance PrettyPrint OpAttr where 
    printText0 ga oa = case oa of
        BinOpAttr a _ -> printText0 ga a
        UnitOpAttr t _ -> text unitS <+> printText0 ga t

instance PrettyPrint DatatypeDecl where 
    printText0 ga (DatatypeDecl p k as d _) = (printText0 ga p <>
					       printKind ga k)
				  <+> text defnS
				  <+> vcat(punctuate (text " | ") 
					   (map (printText0 ga) as))
				  <+> case d of [] -> empty
						_ -> text derivingS
							  <+> commaT_text ga d

instance PrettyPrint Alternative where 
    printText0 ga alt = case alt of
        Constructor n cs p _ -> 
 	    printText0 ga n <+> fsep (map (parens . semiT_text ga) cs)
		       <> printText0 ga p
        Subtype l _ -> text typeS <+> commaT_text ga l

instance PrettyPrint Component where
    printText0 ga sel = case sel of
        Selector n p t _ _ -> printText0 ga n 
			      <+> colon <> printText0 ga p
				      <+> printText0 ga t
        NoSelector t -> printText0 ga t

instance PrettyPrint OpId where 
    printText0 ga (OpId n ts _) = printText0 ga n 
				  <+> noPrint (null ts) 
				      (brackets $ commaT_text ga ts)

instance PrettyPrint Symb where
    printText0 ga (Symb i mt _) =
	printText0 ga i <> (case mt of Nothing -> empty
			               Just (SymbType t) -> 
					  empty <+> colon <+>
					    printText0 ga t)

instance PrettyPrint SymbItems where
    printText0 ga (SymbItems k syms _ _) =
	printSK k <> commaT_text ga syms

instance PrettyPrint SymbOrMap where
    printText0 ga (SymbOrMap s mt _) =
	printText0 ga s <> (case mt of Nothing -> empty
			               Just t -> 
					  empty <+> ptext mapsTo <+>
					    printText0 ga t)

instance PrettyPrint SymbMapItems where
    printText0 ga (SymbMapItems k syms _ _) =
	printSK k <> commaT_text ga syms

-- | print symbol kind
printSK :: SymbKind -> Doc
printSK k = 
    case k of Implicit -> empty
	      _ -> ptext (drop 3 $ show k) <> space 

