{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable 
   
   latex output of the abstract syntax
-}

module HasCASL.LaTeX_HasCASL where

import HasCASL.As
import HasCASL.AsUtils
import HasCASL.Le
import HasCASL.Morphism
import HasCASL.HToken

import Common.PrettyPrint
import Common.Keywords
import Common.Lib.Pretty
import Common.Id
import Common.PrettyPrint
import Common.GlobalAnnotations(GlobalAnnos)
import Common.AS_Annotation(mapAnM)
import Common.PrintLaTeX
import Common.LaTeX_utils
import qualified Common.Lib.Map as Map

-- | short cut for: if b then empty else d
noPrint :: Bool -> Doc -> Doc
noPrint b d = if b then empty else d

instance PrintLaTeX Variance where 
    printLatex0 _ v = text $ show v

instance PrintLaTeX Kind where
    printLatex0 ga knd = case knd of
        Universe _ -> text "Type"
        MissingKind -> space
        ClassKind ci _ -> printLatex0 ga ci
        Downset mt t _ _ -> 
	    let tok = case mt of 
		    Nothing -> text "\\_" 
		    Just x -> (printLatex0 ga x) <+> hc_sty_axiom "\\bullet" <+> (printLatex0 ga x)
	    in braces_latex (tok <+>
		       hc_sty_axiom lessS <+> printLatex0 ga t)
        Intersection ks _ -> printList0 ga ks
        FunKind k1 k2 _ -> 
			  (case k1 of 
				  ExtKind (FunKind _ _ _) InVar _ -> parens
				  FunKind _ _ _ -> parens
				  _ -> id) (printLatex0 ga k1)
			  <+> hc_sty_axiom "\\rightarrow" 
			  <+> printLatex0 ga k2
        ExtKind k v _ -> (case v of
	       InVar -> id 
	       _ -> case k of
		    FunKind _ _ _ -> parens
		    _ -> id) (printLatex0 ga k) <> printLatex0 ga v

instance PrintLaTeX TypePattern where 
    printLatex0 ga tp = case tp of
        TypePattern name args _ -> printLatex0 ga name
				 <> fcat (map (parens . printLatex0 ga) args)
        TypePatternToken t -> printLatex0 ga t
        MixfixTypePattern ts -> fsep_latex (map (printLatex0 ga) ts)
        BracketTypePattern k l _ -> bracket k $ commaT_latex ga l
        TypePatternArg t _ -> parens $ printLatex0 ga t

-- | put proper brackets around a document
bracket :: BracketKind -> Doc -> Doc
bracket b t = let (o,c) = getBrackets b in ptext o <> t <> ptext c

-- | print a 'Kind' plus a preceding colon (or nothing for 'star')
printKind :: GlobalAnnos -> Kind -> Doc
printKind ga kind = case kind of 
		    Universe _ -> empty
		    Downset Nothing t _ _ -> 
			space <> hc_sty_axiom lessS <+> printLatex0 ga t
		    _ -> space <> colon <+> printLatex0 ga kind

instance PrintLaTeX Type where 
    printLatex0 ga ty = case ty of
        TypeName name _k _i -> printLatex0 ga name 
        TypeAppl t1 t2 -> case t1 of 
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
        TypeToken t -> printLatex0 ga t
        BracketType k l _ -> bracket k $ commaT_latex ga l
        KindedType t kind _ -> (case t of 
				FunType _ _ _ _ -> parens
				ProductType [] _ -> id
				ProductType _ _ -> parens
				LazyType _ _ -> parens
				TypeAppl _ _ -> parens
				_ -> id) (printLatex0 ga t) 
				       <+> colon <+> printLatex0 ga kind
        MixfixType ts -> fsep_latex (map (printLatex0 ga) ts)
        LazyType t _ -> hc_sty_axiom quMark <+> (case t of 
					 FunType _ _ _ _ -> parens
					 ProductType [] _ -> id
					 ProductType _ _ -> parens
					 KindedType _ _ _ -> parens
					 _ -> id) (printLatex0 ga t)  
        ProductType ts _ -> if null ts then hc_sty_plain_keyword "Unit"
				       -- parens empty 
			  else fsep_latex (punctuate (space <> char '*') 
				     (map ( \ t -> 
					    (case t of 
					    FunType _ _ _ _ -> parens
					    ProductType [] _ -> id
					    ProductType _ _ -> parens
					    _ -> id) $ printLatex0 ga t) ts))
        FunType t1 arr t2 _ -> (case t1 of 
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
				     fsep_latex (punctuate space
				     (map (printLatex0 ga) ts))
				     
instance PrintLaTeX t => PrintLaTeX (Qual t) where
    printLatex0 ga (ps :=> t) = (if null ps then empty
			       else parens $ commaT_latex ga ps <+>
				    hc_sty_axiom implS <+> space) <>
					       printLatex0 ga t

-- no curried notation for bound variables 
instance PrintLaTeX TypeScheme where
    printLatex0 ga (TypeScheme vs t _) = let tdoc = printLatex0 ga t in 
	if null vs then tdoc else 
	   hang (hc_sty_axiom forallS <+> semiT_latex ga vs <+> hc_sty_axiom "\\bullet") 2 tdoc

instance PrintLaTeX Instance where 
    printLatex0 _ i = case i of
        Instance -> space <> hc_sty_axiom instanceS
	Plain -> empty 

instance PrintLaTeX Partiality where
    printLatex0 _ p = case p of
        Partial -> hc_sty_axiom quMark
	Total -> empty 

instance PrintLaTeX Arrow where 
    printLatex0 _ a = case a of 
        FunArr -> hc_sty_axiom "\\rightarrow"
        PFunArr -> hc_sty_axiom ("\\rightarrow" ++ quMark)
        ContFunArr -> hc_sty_axiom "\\stackrel{c}{\\rightarrow}"
        PContFunArr -> hc_sty_axiom ("\\stackrel{c}{\\rightarrow}" ++ quMark)

instance PrintLaTeX Quantifier where 
    printLatex0 _ Universal = hc_sty_axiom "\\forall"
    printLatex0 _ Existential = hc_sty_axiom "\\exists"
    printLatex0 _ Unique = hc_sty_axiom "\\exists!"

instance PrintLaTeX TypeQual where 
    printLatex0 _ q = text $ show q

instance PrintLaTeX Term where
    printLatex0 ga t = printTerm ga 
	   (case t of 
		  QualVar _ _ _ -> True
		  QualOp _ _ _ _ -> True
		  _ -> False) t

unPredType :: Type -> Type
unPredType t = case t of
	       FunType ty PFunArr (ProductType [] _) _ -> ty
	       _ -> t

unPredTypeScheme :: TypeScheme -> TypeScheme
unPredTypeScheme = mapTypeOfScheme unPredType

substituteArgs :: GlobalAnnos -> [Token] -> [Doc] -> Doc
substituteArgs _ [] ds = cat ds
substituteArgs ga ts [] = cat (map (printLatex0 ga) ts)
substituteArgs ga (t:ts) (d:ds) = 
  if isPlace t 
    then d <+> substituteArgs ga ts ds
    else printLatex0 ga t <+>  substituteArgs ga ts (d:ds)


findMixfixOp :: Term -> Maybe Id
findMixfixOp (QualOp _ (InstOpId ident _ _) _ _) =
  if isMixfix ident then Just ident else Nothing
findMixfixOp (ApplTerm t1 _ _) = findMixfixOp t1
findMixfixOp _ = Nothing

printTerm :: GlobalAnnos -> Bool -> Term -> Doc
printTerm ga b trm = 
    let ppParen = if b then parens else id 
	commaT = fsep_latex . punctuate comma . map (printTerm ga False)
    in
	(case trm of
	       TupleTerm _ _ -> id
	       BracketTerm _ _ _ -> id
	       TermToken _ -> id
	       MixTypeTerm _ _ _ -> id
               _ -> ppParen)
      $ case trm of
        QualVar v _t _ -> printLatex0 ga v
                         {-sep [hc_sty_axiom varS <+> printLatex0 ga v,
			      colon <+> printLatex0 ga t]-}
        QualOp _br n _t _ -> printLatex0 ga n
                           {-sep [printLatex0 ga br <+> printLatex0 ga n,
			        colon <+> printLatex0 ga 
				(if isPred br then unPredTypeScheme t else t)]-}
        ResolvedMixTerm n ts _ -> 
	    case ts of 
	    [] ->  printLatex0 ga n
	    [t] -> printLatex0 ga n <> printTerm ga True t
	    _ -> printLatex0 ga n <> 
		 parens (commaT ts)
        ApplTerm t1 t2 _ -> 
          case (findMixfixOp t1,t2) of
            (Just (Id toks [] _), TupleTerm ts _) -> 
               if length (filter isPlace toks) == length ts
                 then substituteArgs ga toks (map (printTerm ga True) ts) 
                 else cat [printLatex0 ga t1, nest 2
			    $ printTerm ga True t2]
            _ -> cat [printLatex0 ga t1, nest 2
			    $ printTerm ga True t2]
        TupleTerm ts _ -> parens (commaT ts)
        TypedTerm term q typ _ -> hang (printLatex0 ga term
			  <+> printLatex0 ga q)
			  4 $ printLatex0 ga typ
        QuantifiedTerm q vs t _ -> printLatex0 ga q
					  <+> semiT_latex ga vs 
					  <+> hc_sty_axiom "\\bullet"    
					  <+> printLatex0 ga t
        LambdaTerm ps q t _ -> hang (hc_sty_axiom lamS
				      <+> (case ps of
					   [p] -> printLatex0 ga p
					   _ -> fcat $ map 
					      (parens . printTerm ga False) ps)
				      <+> (case q of 
					   Partial -> hc_sty_axiom "\\bullet"
					   Total -> hc_sty_axiom $ "\\bullet" ++ exMark))
				      2 $ printLatex0 ga t
        CaseTerm t es _  -> hang (hc_sty_axiom caseS
				   <+> printLatex0 ga t
				   <+> hc_sty_axiom ofS)
				   4 $ vcat (punctuate (hc_sty_axiom " | ")
					     (map (printEq0 ga "\\rightarrow") es))
        LetTerm br es t _ -> 
	    let dt = printLatex0 ga t
	        des = vcat $ punctuate semi $
		      map (printEq0 ga equalS) es
		in case br of 
		Let -> sep [hc_sty_axiom letS <+> des, hc_sty_axiom inS <+> dt]
		Where -> hang (sep [dt, hc_sty_axiom whereS]) 6 des 
        TermToken t -> printLatex0 ga t
        MixTypeTerm q t _ -> printLatex0 ga q <+> printLatex0 ga t
        MixfixTerm ts -> fsep_latex $ map (printLatex0 ga) ts
        BracketTerm k l _ -> bracket k $ commaT l
        AsPattern v p _ -> printLatex0 ga v
			  <+> hc_sty_axiom asP
			  <+> printLatex0 ga p

-- | print an equation with different symbols between 'Pattern' and 'Term'
printEq0 :: GlobalAnnos -> String -> ProgEq -> Doc
printEq0 ga s (ProgEq p t _) = hang (hang (printLatex0 ga p) 2 $ text s) 
			       4 $ printLatex0 ga t

instance PrintLaTeX VarDecl where 
    printLatex0 ga (VarDecl v t _ _) = printLatex0 ga v <+> colon
						 <+> printLatex0 ga t

instance PrintLaTeX GenVarDecl where 
    printLatex0 ga gvd = case gvd of 
        GenVarDecl v -> printLatex0 ga v
        GenTypeVarDecl tv -> printLatex0 ga tv

instance PrintLaTeX TypeArg where 
    printLatex0 ga (TypeArg v c _ _) = printLatex0 ga v <+> colon 
				      <+> printLatex0 ga c

-- | don't print an empty list and put parens around longer lists
printList0 :: (PrintLaTeX a) => GlobalAnnos -> [a] -> Doc
printList0 ga l =  case l of 
	   []  -> empty
	   [x] -> printLatex0 ga x
	   _   -> parens $ commaT_latex ga l

instance PrintLaTeX InstOpId where
    printLatex0 ga (InstOpId n l _) = 
     (if n==mkId[mkSimpleId place,mkSimpleId "/\\",mkSimpleId place] 
        then hc_sty_axiom "\\wedge"
        else printLatex0 ga n)
     <> noPrint (null l) 
	(brackets $ semiT_latex ga l)

------------------------------------------------------------------------
-- item stuff
------------------------------------------------------------------------
-- | print a 'TypeScheme' as a pseudo type
printPseudoType :: GlobalAnnos -> TypeScheme -> Doc
printPseudoType ga (TypeScheme l t _) = noPrint (null l) (hc_sty_axiom lamS 
				<+> (if null $ tail l then
				     printLatex0 ga $ head l
				     else fcat(map (parens . printLatex0 ga) l))
				<+> hc_sty_axiom "\\bullet" <> space) <> printLatex0 ga t

instance PrintLaTeX BasicSpec where 
    printLatex0 ga (BasicSpec l) = vcat (map (printLatex0 ga) l)

instance PrintLaTeX ProgEq where
    printLatex0 ga = printEq0 ga equalS

instance PrintLaTeX BasicItem where 
    printLatex0 ga bi = case bi of
        SigItems s -> printLatex0 ga s
        ProgItems l _ -> hc_sty_plain_keyword programS <+> semiT_latex ga l
        ClassItems i l _ -> hc_sty_plain_keyword classS <> printLatex0 ga i <+> semiT_latex ga l
        GenVarItems l _ -> hc_sty_plain_keyword varS <+> semiT_latex ga l
        FreeDatatype l _ -> hc_sty_plain_keyword freeS <+> hc_sty_plain_keyword typeS 
				    <+> semiT_latex ga l
        GenItems l _ -> hc_sty_plain_keyword generatedS <+> braces_latex (semiT_latex ga l)
        AxiomItems vs fs _ -> (if null vs then empty
			       else hc_sty_plain_keyword forallS <+> semiT_latex ga vs)
			       $$ vcat (map 
					 (\x -> hc_sty_axiom "\\bullet" <+> printLatex0 ga x) 
					 fs)
        Internal l _ -> hc_sty_plain_keyword internalS <+> braces_latex (semiT_latex ga l)


instance PrintLaTeX OpBrand where
    printLatex0 _ b = text $ show b

instance PrintLaTeX SigItems where 
    printLatex0 ga si = case si of
        TypeItems i l _ -> hc_sty_plain_keyword typeS <> printLatex0 ga i <+> semiT_latex ga l
        OpItems b l _ -> printLatex0 ga b <+> semiT_latex ga 
			 (if isPred b then concat $ 
			  mapAnM ((:[]) . mapOpItem) l else l)

instance PrintLaTeX ClassItem where 
    printLatex0 ga (ClassItem d l _) = printLatex0 ga d $$ 
				   if null l then empty 
				      else braces_latex (semiT_latex ga l)

instance PrintLaTeX ClassDecl where 
    printLatex0 ga (ClassDecl l k _) = commaT_latex ga l 
				      <+> hc_sty_axiom lessS <+> printLatex0 ga k

instance PrintLaTeX Vars where
    printLatex0 ga vd = case vd of
        Var v -> printLatex0 ga v
        VarTuple vs _ -> parens $ commaT_latex ga vs

instance PrintLaTeX TypeItem where 
    printLatex0 ga ti = case ti of
        TypeDecl l k _ -> commaT_latex ga l <> 
				  printKind ga k
        SubtypeDecl l t _ -> commaT_latex ga l <+> hc_sty_axiom lessS 
					<+> printLatex0 ga t
        IsoDecl l _ -> cat(punctuate (hc_sty_axiom " = ") 
				      (map (printLatex0 ga) l))
        SubtypeDefn p v t f _ -> printLatex0 ga p
			       <+> hc_sty_axiom equalS 
			       <+> braces_latex (printLatex0 ga v 
					   <+> colon
					   <+> printLatex0 ga t 
					   <+> hc_sty_axiom "\\bullet"
					   <+> printLatex0 ga f)
        AliasType p k t _ ->  (printLatex0 ga p <>
					  case k of 
					  Nothing -> empty
					  Just j -> space <> colon <+> 
					           printLatex0 ga j)
				       <+> hc_sty_axiom assignS
				       <+> printPseudoType ga t
        Datatype t -> printLatex0 ga t

mapOpItem :: OpItem -> OpItem
mapOpItem oi = case oi of
    OpDecl l t as ps -> OpDecl l (unPredTypeScheme t) as ps
    OpDefn n ps s p t qs -> OpDefn n ps (unPredTypeScheme s) p t qs

instance PrintLaTeX OpItem where 
    printLatex0 ga oi = case oi of
        OpDecl l t as _ -> commaT_latex ga l <+> colon
				   <+> (printLatex0 ga t
					<> (if null as then empty 
					    else comma <> space)
					<> commaT_latex ga as)
        OpDefn n ps s p t _ -> 
	    printLatex0 ga n <> fcat (map (parens . semiT_latex ga) ps)
			    <+> colon <> printLatex0 ga p
 			    <+> printLatex0 ga s 
			    <+> hc_sty_axiom equalS
			    <+> printLatex0 ga t

instance PrintLaTeX BinOpAttr where 
    printLatex0 _ a = hc_sty_axiom $ case a of
        Assoc -> assocS
        Comm -> commS
        Idem -> idemS

instance PrintLaTeX OpAttr where 
    printLatex0 ga oa = case oa of
        BinOpAttr a _ -> printLatex0 ga a
        UnitOpAttr t _ -> hc_sty_axiom unitS <+> printLatex0 ga t

instance PrintLaTeX DatatypeDecl where 
    printLatex0 ga (DatatypeDecl p k as d _) = (printLatex0 ga p <>
					       printKind ga k)
				  <+> hc_sty_axiom defnS
				  <+> vcat(punctuate (hc_sty_axiom " | ") 
					   (map (printLatex0 ga) as))
				  <+> case d of [] -> empty
						_ -> hc_sty_plain_keyword derivingS
							  <+> commaT_latex ga d

instance PrintLaTeX Alternative where 
    printLatex0 ga alt = case alt of
        Constructor n cs p _ -> 
 	    printLatex0 ga n <+> fsep_latex (map (parens . semiT_latex ga) cs)
		       <> printLatex0 ga p
        Subtype l _ -> hc_sty_plain_keyword typeS <+> commaT_latex ga l

instance PrintLaTeX Component where
    printLatex0 ga sel = case sel of
        Selector n p t _ _ -> printLatex0 ga n 
			      <+> colon <> printLatex0 ga p
				      <+> printLatex0 ga t
        NoSelector t -> printLatex0 ga t

instance PrintLaTeX OpId where 
    printLatex0 ga (OpId n ts _) = printLatex0 ga n 
				  <+> noPrint (null ts) 
				      (brackets $ commaT_latex ga ts)

instance PrintLaTeX Symb where
    printLatex0 ga (Symb i mt _) =
	printLatex0 ga i <> (case mt of Nothing -> empty
 			                Just (SymbType t) -> 
					  empty <+> colon <+>
					    printLatex0 ga t)

instance PrintLaTeX SymbItems where
    printLatex0 ga (SymbItems k syms _ _) =
	printSK k <> commaT_latex ga syms

instance PrintLaTeX SymbOrMap where
    printLatex0 ga (SymbOrMap s mt _) =
	printLatex0 ga s <> (case mt of Nothing -> empty
 			                Just t -> 
					  empty <+> hc_sty_axiom "\\mapsto" <+>
					    printLatex0 ga t)

instance PrintLaTeX SymbMapItems where
    printLatex0 ga (SymbMapItems k syms _ _) =
	printSK k <> commaT_latex ga syms

-- | print symbol kind
printSK :: SymbKind -> Doc
printSK k = 
    case k of Implicit -> empty
	      _ -> ptext (drop 3 $ show k) <> space 




------------------------------------- Le -----------------------------------
instance PrintLaTeX ClassInfo where
    printLatex0 ga (ClassInfo ks) =
	   space <> hc_sty_axiom lessS <+> printList0 ga ks

printGenKind :: GenKind -> Doc
printGenKind k = case k of
		Loose -> empty
		Free -> hc_sty_plain_keyword freeS <> space
		Generated -> hc_sty_plain_keyword generatedS <> space

instance PrintLaTeX TypeDefn where
    printLatex0 _ NoTypeDefn = empty
    printLatex0 _ PreDatatype = space <> text "\\%(data type)\\%"
    printLatex0 _ TypeVarDefn = space <> text "\\%(var)\\%"
    printLatex0 ga (AliasTypeDefn s) = space <> hc_sty_axiom assignS 
				      <+> printPseudoType ga s
    printLatex0 ga (Supertype v t f) = space <> hc_sty_axiom equalS <+> 
					 braces_latex (printLatex0 ga v 
					   <+> colon
					   <+> printLatex0 ga t 
					   <+> hc_sty_axiom "\\bullet"
					   <+> printLatex0 ga f)
    printLatex0 ga (DatatypeDefn de)  = text " \\%[" <>
	printLatex0 ga de <> text "]\\%"

printAltDefn :: GlobalAnnos -> Type -> AltDefn -> Doc
printAltDefn ga dt (Construct mi ts p sels) = case mi of 
        Just i -> printLatex0 ga i <+> colon 
		  <+> printLatex0 ga (getConstrType dt p ts) 
		  <+> fcat (map (parens . semiT_latex ga) sels)
	Nothing -> hc_sty_plain_keyword (typeS ++ sS) <+> commaT_latex ga ts

instance PrintLaTeX Selector where
    printLatex0 ga (Select mi t p) = (case mi of
        Just i -> printLatex0 ga i <+> (case p of 
			     Partial -> hc_sty_axiom ":?"
			     Total -> colon) <> space
	Nothing -> empty) <> printLatex0 ga t

instance PrintLaTeX TypeInfo where
    printLatex0 ga (TypeInfo _ ks sups defn) =
	space <> colon <+> printList0 ga ks
	<> noPrint (null sups)
	   (space <> hc_sty_axiom lessS <+> printList0 ga sups)
        <> printLatex0 ga defn

instance PrintLaTeX ConstrInfo where
    printLatex0 ga (ConstrInfo i t) = 
	printLatex0 ga i <+> colon <+> printLatex0 ga t

instance PrintLaTeX OpDefn where
    printLatex0 _ (NoOpDefn b) = space <> text ("\\%(" ++ show b ++ ")\\%")
    printLatex0 _ VarDefn = space <> text "\\%(var)\\%"
    printLatex0 _ (ConstructData i) = space <> text ("\\%(construct " ++
				     showId i ")\\%")
    printLatex0 ga (SelectData c i) = space <> text ("\\%(select from " ++
				     showId i " constructed by")
				    $$ printList0 ga c <> text ")\\%"
    printLatex0 ga (Definition b t) = printLatex0 ga (NoOpDefn b) <+> 
				     hc_sty_axiom equalS <+> printLatex0 ga t
 
instance PrintLaTeX OpInfo where
    printLatex0 ga o = space <> colon <+> printLatex0 ga (opType o)
		      <> (case opAttrs o of 
			  [] -> empty 
			  l -> comma <> commaT_latex ga l)
		      <>  printLatex0 ga (opDefn o)
 
instance PrintLaTeX OpInfos where
    printLatex0 ga (OpInfos l) = vcat $ map (printLatex0 ga) l

instance PrintLaTeX DataEntry where 
    printLatex0 ga (DataEntry im i k args alts) =  
	printGenKind k <> hc_sty_plain_keyword typeS <+> printLatex0 ga i 
	     <> hcat (map (parens . printLatex0 ga) args)
	    <+> (hc_sty_axiom defnS $$ 
		 vcat (map (printAltDefn ga $ typeIdToType i args star) alts))
	$$ nest 2 (noPrint (Map.isEmpty im) 
	   (hc_sty_plain_keyword withS <+> hc_sty_plain_keyword (typeS ++ sS) 
		   <+> printMap0 ga (hc_sty_axiom mapsTo) im))

instance PrintLaTeX Sentence where 
    printLatex0 ga s = case s of
        Formula t -> printLatex0 ga t
	DatatypeSen ls -> vcat (map (printLatex0 ga) ls)
        ProgEqSen _ _ pe -> hc_sty_plain_keyword programS 
			    <+> printLatex0 ga pe
 
instance PrintLaTeX Env where
    printLatex0 ga (Env{classMap=cm, typeMap=tm, 
		       assumps=as, sentences=se, envDiags=_ds}) = 
	noPrint (Map.isEmpty cm) (header "Classes")
	$$ printMap0 ga empty cm
	$$ noPrint (Map.isEmpty tm) (header "Type Constructors")
	$$ printMap0 ga empty tm
	$$ noPrint (Map.isEmpty as) (header "Assumptions")
        $$ printMap0 ga empty as
	$$ noPrint (null se) (header "Sentences")
        $$ vcat (map (printLatex0 ga) se)
--	$$ noPrint (null ds) (header "Diagnostics")
--	$$ vcat (map (printLatex0 ga) $ reverse ds)
	where header s =  text "\\%\\%" <+> text s 
			  <+> text (replicate (70 - length s) '-')

printMap0 :: (PrintLaTeX a, Ord a, PrintLaTeX b)  
			   => GlobalAnnos -> Doc -> Map.Map a b -> Doc
printMap0 g d m =let l = Map.toList m in
    vcat(map (\ (a, b) -> printLatex0 g a <> d <> printLatex0 g b) l)

instance PrintLaTeX SymbolType where
    printLatex0 ga t = case t of 
      OpAsItemType sc -> printLatex0 ga sc
      TypeAsItemType k -> printLatex0 ga k
      ClassAsItemType k -> printLatex0 ga k

instance PrintLaTeX Symbol where
    printLatex0 ga s = hc_sty_plain_keyword (case symType s of 
			    OpAsItemType _ -> opS
			    TypeAsItemType _ -> typeS
			    ClassAsItemType _ -> classS) <+> 
                    printLatex0 ga (symName s) <+> hc_sty_axiom colonS <+> 
		    printLatex0 ga (symType s)

instance PrintLaTeX RawSymbol where
  printLatex0 ga rs = case rs of
      AnID i -> printLatex0 ga i
      AKindedId k i -> printSK k <> printLatex0 ga i
      AQualId i t -> printSK (symbTypeToKind t) <> printLatex0 ga i <+> colon 
		       <+> printLatex0 ga t


------------------------------- Morphism ------------------------------------
instance PrintLaTeX Morphism where
  printLatex0 ga m = braces_latex (printLatex0 ga (msource m)) 
		    $$ hc_sty_axiom "\\mapsto"
		    <+> braces_latex (printLatex0 ga (mtarget m))
