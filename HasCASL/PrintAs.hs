
{- HetCATS/HasCASL/PrintAs.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   printing As data types
-}

module PrintAs where

import As
import Keywords
import HToken
import Pretty
import PrettyPrint

commas l = fsep $ punctuate comma (map printText0 l)
semis l = sep $ punctuate semi (map printText0 l)

instance PrettyPrint TypePattern where 
    printText0(TypePattern name args _) = printText0(name) 
				 <> fcat (map (parens.printText0) args)
    printText0(TypePatternToken t) = printText0(t)
    printText0(MixfixTypePattern ts) = fsep (map printText0 ts)
    printText0(BracketTypePattern k l _) = bracket k $ commas l
    printText0(TypePatternArgs l) = semis l

bracket Parens t = parens t
bracket Squares t = Pretty.brackets t
bracket Braces t = braces t

instance PrettyPrint Type where 
    printText0(TypeConstrAppl name kind args _) = printText0 name 
			  <> (case kind of 
			       Kind [] (Universe _) _ -> empty
			       _ -> space <> colon <> printText0(kind))
			  <> if null args then empty else parens (commas args)
    printText0(TypeToken t) = printText0(t)
    printText0(BracketType k l _) = bracket k $ commas l
    printText0(KindedType t kind _) = printText0(t)  
			  <> (case kind of 
			       Kind [] (Universe _) _ -> empty
			       _ -> space <> colon <> printText0(kind))
    printText0(MixfixType ts) = fsep (map printText0 ts)
    printText0(TupleType args _) = parens $ commas args
    printText0(LazyType t _) = text quMark <+> printText0(t)  
    printText0(ProductType ts _) = fsep (punctuate (space <> text timesS) 
					 (map printText0 ts))
    printText0(FunType t1 arr t2 _) = printText0 t1
				      <+> printText0 arr
				      <+> printText0 t2

-- no curried notation for bound variables 
instance PrettyPrint TypeScheme where
    printText0(SimpleTypeScheme t) = printText0 t
    printText0(TypeScheme vs t _) = text forallS
				   <+> semis vs 
				   <+> text dotS
				   <+> printText0 t

instance PrettyPrint Partiality where
    printText0 Partial = text quMark
    printText0 Total = text exMark

instance PrettyPrint Arrow where 
    printText0 FunArr = text funS
    printText0 PFunArr = text pFun
    printText0 ContFunArr = text contFun
    printText0 PContFunArr = text pContFun 


instance PrettyPrint Quantifier where 
    printText0 Universal = text forallS
    printText0 Existential = text existsS 
    printText0 Unique = text $ existsS ++ exMark

instance PrettyPrint TypeQual where 
    printText0 OfType = colon
    printText0 AsType = text asS
    printText0 InType = text inS

instance PrettyPrint Formula where
    printText0 (TermFormula t) = printText0 t
-- other cases missing

instance PrettyPrint Term where
    printText0(CondTerm t1 f t2 _) =  printText0 t1
				      <+> text whenS
				      <+> printText0 f
				      <+> text elseS
				      <+> printText0 t2
    printText0(QualVar v t _) = parens $ text varS
			<+> printText0 v
			<+> colon
			<+> printText0 t
    printText0(QualOp n t _) = parens $
			text opS 
			<+> printText0 n
			<+> colon
			<+> printText0 t
    printText0(ApplTerm t1 t2 _) = printText0 t1
			<+> parens (printText0 t2)
    printText0(TupleTerm ts _) = parens $ commas ts 
    printText0(TypedTerm term q typ _) = printText0 term
			  <+> printText0 q
			  <+> printText0 typ
    printText0(QuantifiedTerm q vs t _) = printText0 q
					  <+> semis vs 
					  <+> text dotS    
					  <+> printText0 t
    printText0(LambdaTerm ps q t _) = text lamS
				      <+> (if length ps == 1 then 
					     printText0 $ head ps
					     else fcat $ map 
					   (parens.printText0) ps)
				      <+> (case q of 
					   Partial -> text dotS
					   Total -> text $ dotS ++ exMark)
				      <+> printText0 t
    printText0(CaseTerm t es _ ) = text caseS
				   <+> printText0 t
				   <+> text ofS
				   <+> vcat (punctuate (text " | ")
					     (map (printEq0 funS) es))
    printText0(LetTerm es t _) =  text letS
				   <+> vcat (punctuate semi
					     (map (printEq0 equalS) es))
				   <+> text inS
				   <+> printText0 t
    printText0(TermToken t) = printText0 t
    printText0(MixfixTerm ts) = fsep $ map printText0 ts
    printText0(BracketTerm k l _) = bracket k $ commas l

instance PrettyPrint Pattern where 
    printText0(PatternVars vs _) = semis vs
    printText0(PatternConstr n t args _) = printText0 n 
			  <+> colon
			  <+> printText0 t 
			  <+> fcat (map (parens.printText0) args)
    printText0(PatternToken t) = printText0 t
    printText0(BracketPattern  k l _) = bracket k $ commas l
    printText0(TuplePattern ps _) = parens $ commas ps
    printText0(MixfixPattern ps) = fsep (map printText0 ps)
    printText0(TypedPattern p t _) = printText0 p 
			  <+> colon
			  <+> printText0 t 
    printText0(AsPattern v p _) = printText0 v
			  <+> text asP
			  <+> printText0 p

printEq0 s (ProgEq p t _) = fsep [printText0 p 
			  , text s
			  , printText0 t] 

instance PrettyPrint VarDecl where 
    printText0(VarDecl v t _ _) = printText0 v <+> colon
						 <+> printText0 t

instance PrettyPrint TypeVarDecl where 
    printText0(TypeVarDecl v c _ _) = printText0 v <+> 
					      case c of 
					      Downset t -> 
					        text lessS <+> printText0 t
					      _ -> colon <+> printText0 c

instance PrettyPrint GenVarDecl where 
    printText0(GenVarDecl v) = printText0 v
    printText0(GenTypeVarDecl tv) = printText0 tv

instance PrettyPrint TypeArg where 
    printText0 (TypeArg v c _ _) = printText0 v <> colon <> printText0 c

instance PrettyPrint Variance where 
    printText0 CoVar = text plusS
    printText0 ContraVar = text minusS
    printText0 InVar = empty

instance PrettyPrint ExtClass where 
    printText0(ExtClass c v _) = printText0 c <> printText0 v <> space

instance PrettyPrint ProdClass where 
    printText0(ProdClass l _) = fcat $ punctuate (text timesS) 
			       (map printText0 l)

instance PrettyPrint Kind where 
    printText0(Kind l c _) = (if null l then empty else 
			      (fcat $ punctuate (text funS) 
			       (map printText0 l))
			      <> text funS) 
			     <> printText0 c

instance PrettyPrint Class where 
    printText0(Universe _) = empty
    printText0(ClassName n) = printText0 n
    printText0(Downset t) = braces $ text lessS <+> printText0 t
    printText0(Intersection c _) = parens $ commas c 

instance PrettyPrint Types where
    printText0(Types l _) = Pretty.brackets $ commas l

instance PrettyPrint InstOpName where
    printText0 (InstOpName n l) = printText0 n <> fcat(map printText0 l)

------------------------------------------------------------------------
-- item stuff
------------------------------------------------------------------------
instance PrettyPrint PseudoType where 
    printText0 (SimplePseudoType t) = printText0 t
    printText0 (PseudoType l t _) = text lamS <+> fcat(map printText0 l)
				<+> text dotS <+> printText0 t

instance PrettyPrint TypeArgs where
    printText0 (TypeArgs l _) = semis l

instance PrettyPrint TypeVarDecls where 
    printText0 (TypeVarDecls l _) = Pretty.brackets $ semis l

instance PrettyPrint BasicSpec where 
    printText0 (BasicSpec l) = vcat (map printText0 l)

instance PrettyPrint ProgEq where
    printText0 = printEq0 equalS

instance PrettyPrint BasicItem where 
    printText0 (SigItems s) = printText0 s
    printText0 (ProgItems l _) = text programS <+> semis l
    printText0 (ClassItems i l _) = text classS <+> printText0 i
			       <+> semis l
    printText0 (GenVarItems l _) = text varS <+> semis l
    printText0 (FreeDatatype l _) = text freeS <+> text typeS 
				    <+> semis l
    printText0 (GenItems l _) = text generatedS <+> braces (semis l)
    printText0 (LocalVarAxioms vs fs p) = text forallS 
			       <+> semis vs
			       $$ printText0(AxiomItems fs p)
    printText0 (AxiomItems fs _) = vcat (map 
					 (\x -> text dotS <+> printText0 x) 
					 fs)

instance PrettyPrint SigItems where 
    printText0 (TypeItems i l _) = text typeS <+> printText0 i <+> semis l
    printText0 (OpItems l _) = text opS <+> semis l
    printText0 (PredItems l _) = text predS <+> semis l

instance PrettyPrint Instance where
    printText0 Instance = text instanceS
    printText0 _ = empty
		      
instance PrettyPrint ClassItem where 
    printText0 (ClassItem d l _) = printText0 d $$ 
				   if null l then empty else braces (semis l)

instance PrettyPrint ClassDecl where 
    printText0 (ClassDecl l _) = commas l
    printText0 (SubclassDecl l s _) = commas l <> text lessS <> printText0 s
    printText0 (ClassDefn n c _) =  printText0 n 
			       <> text equalS 
			       <> printText0 c
    printText0 (DownsetDefn c v t _) = printText0 c
			       <> text equalS 
			       <> braces (printText0 v 
					   <> text dotS
					   <> printText0 v 
					   <> (text lessS
					       <+> printText0 t))

instance PrettyPrint TypeItem where 
    printText0 (TypeDecl l k _) = commas l <> 
				  case k of 
				  Kind [] (Universe _) _ -> empty
				  _ -> space <> colon <> printText0 k
    printText0 (SubtypeDecl l t _) = commas l <+> text lessS <+> printText0 t
    printText0 (IsoDecl l _) = cat(punctuate (text " = ") (map printText0 l) )
    printText0 (SubtypeDefn p v t f _) = printText0 p
			       <+> text equalS 
			       <+> braces (printText0 v 
					   <+> colon
					   <+> printText0 t 
					   <+> text dotS
					   <+> printText0 f)
    printText0 (AliasType p k t _) =  (printText0 p <>
				       case k of 
				       Kind [] (Universe _) _ -> empty
				       _ -> space <> colon <> printText0 k)
				       <+> text assignS
				       <+> printText0 t
    printText0 (Datatype t) = printText0 t

instance PrettyPrint OpItem where 
    printText0 (OpDecl l t as _) = commas l <+> colon
				   <+> (printText0 t
					<> (if null as then empty else comma)
					<> commas as)
    printText0 (OpDefn n ps s p t _) = (printText0 n 
					<> fcat (map printText0 ps))
			    <+> (colon <> if p == Partial 
				 then text quMark else empty)
 			    <+> printText0 s 
			    <+> text equalS
			    <+> printText0 t

instance PrettyPrint PredItem where 
    printText0 (PredDecl l t _) = commas l <+> colon <+> printText0 t
    printText0 (PredDefn n ps f _) = (printText0 n <> fcat (map printText0 ps))
				     <+> text equivS
				     <+> printText0 f

instance PrettyPrint BinOpAttr where 
    printText0 Assoc = text assocS
    printText0 Comm = text commS
    printText0 Idem = text idemS

instance PrettyPrint OpAttr where 
    printText0 (BinOpAttr a _) = printText0 a
    printText0 (UnitOpAttr t _) = text unitS <+> printText0 t

instance PrettyPrint DatatypeDecl where 
    printText0 (DatatypeDecl p k as d _) = (printText0 p <>
				       case k of 
				       Kind [] (Universe _) _ -> empty
				       _ -> space <> colon <> printText0 k)
				  <+> text defnS
				  <+> vcat(punctuate (text " | ") 
					   (map printText0 as))
				  <+> case d of { Nothing -> empty
						; Just c -> text derivingS
						  <+> printText0 c
						}

instance PrettyPrint Alternative where 
    printText0 (Constructor n cs p _) = printText0 n 
					<> fcat (map printText0 cs)
					<> (case p of {Partial -> text quMark;
						       _ -> empty})
    printText0 (Subtype l _) = text typeS <+> commas l

instance PrettyPrint Components where 
    printText0 (Selector n p t _ _) = printText0 n 
				<> colon <> (case p of { Partial ->text quMark;
							 _ -> empty } 
					      <+> printText0 t)
    printText0 (NoSelector t) = printText0 t
    printText0 (NestedComponents l _) = parens $ semis l

instance PrettyPrint OpName where 
    printText0 (OpName n ts) = printText0 n <+> fcat(map printText0 ts)

