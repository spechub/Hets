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

-- | short cut for: if b then empty else d
noPrint :: Bool -> Doc -> Doc
noPrint b d = if b then empty else d

instance PrettyPrint Variance where 
    printText0 _ CoVar = text plusS
    printText0 _ ContraVar = text minusS
    printText0 _ InVar = empty

instance PrettyPrint Kind where
    printText0 _ (Universe _) = text "Type"
    printText0 _ MissingKind = space
    printText0 ga (ClassKind ci _) = printText0 ga ci
    printText0 ga (Downset mt t _ _) =
	let tok = case mt of 
		  Nothing -> text "_" 
		  Just x -> text (tokStr x) <+> text dotS <+> text (tokStr x)
	    in braces (tok <+>
		       text lessS <+> printText0 ga t)
    printText0 ga (Intersection ks _) = printList0 ga ks
    printText0 ga (FunKind k1 k2 _) = 
			  (case k1 of 
				  ExtKind (FunKind _ _ _) InVar _ -> parens
				  FunKind _ _ _ -> parens
				  _ -> id) (printText0 ga k1)
			  <+> text funS 
			  <+> printText0 ga k2
    printText0 ga (ExtKind k v _) = 
	(case v of
	       InVar -> id 
	       _ -> case k of
		    FunKind _ _ _ -> parens
		    _ -> id) (printText0 ga k) <> printText0 ga v

instance PrettyPrint TypePattern where 
    printText0 ga (TypePattern name args _) = printText0 ga name
				 <> fcat (map (parens . printText0 ga) args)
    printText0 ga (TypePatternToken t) = printText0 ga t
    printText0 ga (MixfixTypePattern ts) = fsep (map (printText0 ga) ts)
    printText0 ga (BracketTypePattern k l _) = bracket k $ commaT_text ga l
    printText0 ga (TypePatternArg t _) = parens $ printText0 ga t

-- | put proper brackets around a document
bracket :: BracketKind -> Doc -> Doc
bracket b t = let (o,c) = getBrackets b in ptext o <> t <> ptext c

-- | print a 'Kind' plus a preceding colon (or nothing for 'star')
printKind :: GlobalAnnos -> Kind -> Doc
printKind ga kind = case kind of 
		    Universe _ -> empty
		    Downset Nothing t _ _ -> 
			space <> text lessS <+> printText0 ga t
		    _ -> space <> colon <+> printText0 ga kind

instance PrettyPrint Type where 
    printText0 ga (TypeName name _k _i) = printText0 ga name 
    printText0 ga (TypeAppl t1 t2) = 
        case t1 of 
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
    printText0 ga (TypeToken t) = printText0 ga t
    printText0 ga (BracketType k l _) = bracket k $ commaT_text ga l
    printText0 ga (KindedType t kind _) = (case t of 
					    FunType _ _ _ _ -> parens
					    ProductType [] _ -> id
					    ProductType _ _ -> parens
					    LazyType _ _ -> parens
					    TypeAppl _ _ -> parens
					    _ -> id) (printText0 ga t) 
					  <+> colon <+> printText0 ga kind
    printText0 ga (MixfixType ts) = fsep (map (printText0 ga) ts)
    printText0 ga (LazyType t _) = text quMark <+> (case t of 
					    FunType _ _ _ _ -> parens
					    ProductType [] _ -> id
					    ProductType _ _ -> parens
					    KindedType _ _ _ -> parens
					    _ -> id) (printText0 ga t)  
    printText0 ga (ProductType ts _) = if null ts then ptext "Unit"
				       -- parens empty 
			  else fsep (punctuate (space <> text timesS) 
				     (map ( \ t -> 
					    (case t of 
					    FunType _ _ _ _ -> parens
					    ProductType [] _ -> id
					    ProductType _ _ -> parens
					    _ -> id) $ printText0 ga t) ts))
    printText0 ga (FunType t1 arr t2 _) = (case t1 of 
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
    printText0 ga (TypeScheme vs t _) = noPrint (null vs) (text forallS
						    <+> semiT_text ga vs 
						    <+> text dotS <+> space)
					 <> printText0 ga t

instance PrettyPrint Partiality where
    printText0 _ Partial = text quMark
    printText0 _ Total = text exMark

instance PrettyPrint Arrow where 
    printText0 _ a = text $ show a

instance PrettyPrint Quantifier where 
    printText0 _ Universal = text forallS
    printText0 _ Existential = text existsS 
    printText0 _ Unique = text $ existsS ++ exMark

instance PrettyPrint TypeQual where 
    printText0 _ OfType = colon
    printText0 _ AsType = text asS
    printText0 _ InType = text inS

instance PrettyPrint Term where
    printText0 ga (QualVar v t _) = parens $ text varS
			<+> printText0 ga v
			<+> colon
			<+> printText0 ga t
    printText0 ga (QualOp b n t _) = parens $
			printText0 ga b
			<+> printText0 ga n
			<+> colon
			<+> printText0 ga t
    printText0 ga (ResolvedMixTerm n ts _) = (if isSimpleId n then
					     id else parens) (printText0 ga n)
			<> noPrint (null ts) (parens $ commaT_text ga ts)
    printText0 ga (ApplTerm t1 t2 _) = printText0 ga t1
			<+> (case t2 of 
			     QualVar _ _ _ -> id 
			     QualOp _ _ _ _ -> id 
			     TupleTerm _ _ -> id
			     BracketTerm Parens _ _ -> id
			     ResolvedMixTerm _ [] _ -> id
			     TermToken _ -> id
			     _ -> parens) (printText0 ga t2)
    printText0 ga (TupleTerm ts _) = parens $ commaT_text ga ts 
    printText0 ga (TypedTerm term q typ _) = printText0 ga term
			  <+> printText0 ga q
			  <+> printText0 ga typ
    printText0 ga (QuantifiedTerm q vs t _) = printText0 ga q
					  <+> semiT_text ga vs 
					  <+> text dotS    
					  <+> printText0 ga t
    printText0 ga (LambdaTerm ps q t _) = text lamS
				      <+> (case ps of
					   [p] -> printText0 ga p
					   _ -> fcat $ map 
					        (parens.printText0 ga) ps)
				      <+> (case q of 
					   Partial -> text dotS
					   Total -> text $ dotS ++ exMark)
				      <+> printText0 ga t
    printText0 ga (CaseTerm t es _ ) = text caseS
				   <+> printText0 ga t
				   <+> text ofS
				   <+> vcat (punctuate (text " | ")
					     (map (printEq0 ga funS) es))
    printText0 ga (LetTerm b es t _) = 
	let dt = printText0 ga t
	    des = vcat $ punctuate semi $
		  map (printEq0 ga equalS) es
        in case b of 
		  Let -> text letS <+> des <+> text inS <+> dt
		  Where -> dt <+> text whereS <+> des 
    printText0 ga (TermToken t) = printText0 ga t
    printText0 ga (MixTypeTerm q t _) = printText0 ga q <+> printText0 ga t
    printText0 ga (MixfixTerm ts) = fsep $ map (printText0 ga) ts
    printText0 ga (BracketTerm k l _) = bracket k $ commaT_text ga l

instance PrettyPrint Pattern where 
    printText0 ga (PatternVar v) = printText0 ga v
    printText0 ga (PatternConstr n t _) = printText0 ga n 
			  <+> colon
			  <+> printText0 ga t 
    printText0 ga (ResolvedMixPattern n args _) = 
	(if isSimpleId n then id else parens) (printText0 ga n) 
			     <> (case args of 
				 [] -> empty
				 [t@(TuplePattern _ _)] -> 
				           printText0 ga t
				 _ -> parens $ commaT_text ga args)
    printText0 ga (ApplPattern p1 p2 _) =  printText0 ga p1
			<+> (case p2 of 
			     TuplePattern _ _ -> id
			     BracketPattern Parens _ _ -> id
			     ResolvedMixPattern _ [] _ -> id
			     PatternToken _ -> id
			     _ -> parens) (printText0 ga p2)
    printText0 ga (TuplePattern ps _) = parens $ commaT_text ga ps
    printText0 ga (TypedPattern p t _) = printText0 ga p 
			  <+> colon
			  <+> printText0 ga t 
    printText0 ga (AsPattern v p _) = printText0 ga v
			  <+> text asP
			  <+> printText0 ga p
    printText0 ga (PatternToken t) = printText0 ga t
    printText0 ga (BracketPattern k l _) = bracket k $ commaT_text ga l
    printText0 ga (MixfixPattern ps) = fsep (map (printText0 ga) ps)

-- | print an equation with different symbols between 'Pattern' and 'Term'
printEq0 :: GlobalAnnos -> String -> ProgEq -> Doc
printEq0 ga s (ProgEq p t _) = fsep [printText0 ga p 
			  , text s
			  , printText0 ga t] 

instance PrettyPrint VarDecl where 
    printText0 ga (VarDecl v t _ _) = printText0 ga v <+> colon
						 <+> printText0 ga t

instance PrettyPrint GenVarDecl where 
    printText0 ga (GenVarDecl v) = printText0 ga v
    printText0 ga (GenTypeVarDecl tv) = printText0 ga tv

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
    printText0 ga (SigItems s) = printText0 ga s
    printText0 ga (ProgItems l _) = text programS <+> semiT_text ga l
    printText0 ga (ClassItems i l _) = text classS <+> printText0 ga i
			       <+> semiT_text ga l
    printText0 ga (GenVarItems l _) = text varS <+> semiT_text ga l
    printText0 ga (FreeDatatype l _) = text freeS <+> text typeS 
				    <+> semiT_text ga l
    printText0 ga (GenItems l _) = text generatedS <+> braces (semiT_text ga l)
    printText0 ga (AxiomItems vs fs _) = (if null vs then empty
			       else text forallS <+> semiT_text ga vs)
			       $$ vcat (map 
					 (\x -> text dotS <+> printText0 ga x) 
					 fs)
    printText0 ga (Internal l _) = text internalS <+> braces (semiT_text ga l)


instance PrettyPrint OpBrand where
    printText0 _ b = text $ case b of Fun -> functS 
				      Op -> opS
				      Pred -> "predfun"

instance PrettyPrint SigItems where 
    printText0 ga (TypeItems i l _) = text typeS <+> printText0 ga i 
				      <+> semiT_text ga l
    printText0 ga (OpItems b l _) = printText0 ga b <+> semiT_text ga l

instance PrettyPrint Instance where
    printText0 _ Instance = text instanceS
    printText0 _ _ = empty
		      
instance PrettyPrint ClassItem where 
    printText0 ga (ClassItem d l _) = printText0 ga d $$ 
				   if null l then empty 
				      else braces (semiT_text ga l)

instance PrettyPrint ClassDecl where 
    printText0 ga (ClassDecl l k _) = commaT_text ga l 
				      <+> text lessS <+> printText0 ga k

instance PrettyPrint Vars where
    printText0 ga (Var v) = printText0 ga v
    printText0 ga (VarTuple vs _) = parens $ commaT_text ga vs

instance PrettyPrint TypeItem where 
    printText0 ga (TypeDecl l k _) = commaT_text ga l <> 
				  printKind ga k
    printText0 ga (SubtypeDecl l t _) = commaT_text ga l <+> text lessS 
					<+> printText0 ga t
    printText0 ga (IsoDecl l _) = cat(punctuate (text " = ") 
				      (map (printText0 ga) l))
    printText0 ga (SubtypeDefn p v t f _) = printText0 ga p
			       <+> text equalS 
			       <+> braces (printText0 ga v 
					   <+> colon
					   <+> printText0 ga t 
					   <+> text dotS
					   <+> printText0 ga f)
    printText0 ga (AliasType p k t _) =  (printText0 ga p <>
					  case k of 
					  Nothing -> empty
					  Just j -> space <> colon <+> 
					           printText0 ga j)
				       <+> text assignS
				       <+> printPseudoType ga t
    printText0 ga (Datatype t) = printText0 ga t

instance PrettyPrint OpItem where 
    printText0 ga (OpDecl l t as _) = commaT_text ga l <+> colon
				   <+> (printText0 ga t
					<> (if null as then empty else comma)
					<> commaT_text ga as)
    printText0 ga (OpDefn n ps s p t _) = 
	(printText0 ga n <> fcat (map (parens . semiT_text ga) ps))
			    <+> (colon <> if p == Partial 
				 then text quMark else empty)
 			    <+> printText0 ga s 
			    <+> text equalS
			    <+> printText0 ga t

instance PrettyPrint BinOpAttr where 
    printText0 _ Assoc = text assocS
    printText0 _ Comm = text commS
    printText0 _ Idem = text idemS

instance PrettyPrint OpAttr where 
    printText0 ga (BinOpAttr a _) = printText0 ga a
    printText0 ga (UnitOpAttr t _) = text unitS <+> printText0 ga t

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
    printText0 ga (Constructor n cs p _) = 
	printText0 ga n <+> fsep (map (parens . semiT_text ga) cs)
		       <+> (case p of {Partial -> text quMark;
				       _ -> empty})
    printText0 ga (Subtype l _) = text typeS <+> commaT_text ga l

instance PrettyPrint Component where 
    printText0 ga (Selector n p t _ _) = printText0 ga n 
				<> colon <> (case p of { Partial ->text quMark;
							 _ -> empty } 
					      <+> printText0 ga t)
    printText0 ga (NoSelector t) = printText0 ga t

instance PrettyPrint OpId where 
    printText0 ga (OpId n ts _) = printText0 ga n 
				  <+> noPrint (null ts) 
				      (brackets $ commaT_text ga ts)

