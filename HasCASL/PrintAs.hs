
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

commas l = hcat $ punctuate comma (map printText0 l)
semis l = hcat $ punctuate semi (map printText0 l)

instance PrettyPrint TypePattern where 
    printText0(TypePattern name args _) = printText0(name) 
				 <> hcat (map (parens.printText0) args)
    printText0(TypePatternToken t) = printText0(t)
    printText0(MixfixTypePattern ts) = hsep (map printText0 ts)
    printText0(BracketTypePattern k l _) = bracket k $ commas l
    printText0(TypePatternArgs l) = semis l

bracket Parens t = parens t
bracket Squares t = Pretty.brackets t
bracket Braces t = braces t

instance PrettyPrint Type where 
    printText0(TypeConstrAppl name kind args _) = printText0 name 
			  <+> colon
			  <+> printText0 kind
			  <+> parens (commas args)
    printText0(TypeToken t) = printText0(t)
    printText0(BracketType k l _) = bracket k $ commas l
    printText0(KindedType t kind _) = printText0(t)  
			  <+> colon
			  <+> printText0(kind)
    printText0(MixfixType ts) = hsep (map printText0 ts)
    printText0(TupleType args _) = parens $ commas args
    printText0(LazyType t _) = text quMark <+> printText0(t)  
    printText0(ProductType ts _) = hsep (punctuate (text " *") 
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

instance PrettyPrint PartialKind where
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
					     else hcat $ map 
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
    printText0(MixfixTerm ts) = hsep (map printText0 ts)
    printText0(BracketTerm k l _) = bracket k $ commas l

instance PrettyPrint Pattern where 
    printText0(PatternVars vs _) = semis vs
    printText0(PatternConstr n t args _) = printText0 n 
			  <+> colon
			  <+> printText0 t 
			  <+> hcat (map (parens.printText0) args)
    printText0(PatternToken t) = printText0 t
    printText0(BracketPattern  k l _) = bracket k $ commas l
    printText0(TuplePattern ps _) = parens $ commas ps
    printText0(MixfixPattern ps) = hsep (map printText0 ps)
    printText0(TypedPattern p t _) = printText0 p 
			  <+> colon
			  <+> printText0 t 
    printText0(AsPattern v p _) = printText0 v
			  <+> text asP
			  <+> printText0 p


printEq0 s (ProgEq p t _) = printText0 p 
			  <+> text s
			  <+> printText0 t 

instance PrettyPrint VarDecl where 
    printText0(VarDecl v t k _) = case k of Comma -> printText0 v <> comma
					    _ -> printText0 v <+> colon
						 <+> printText0 t

instance PrettyPrint TypeVarDecl where 
    printText0(TypeVarDecl v c k _) = case k of 
				      Comma -> printText0 v <> comma
				      _ -> printText0 v <+> 
					      case c of 
					      Downset t -> 
					        text lessS <+> printText0 t
					      _ -> colon <+> printText0 c

instance PrettyPrint GenVarDecl where 
    printText0(GenVarDecl v) = printText0 v
    printText0(GenTypeVarDecl tv) = printText0 tv

instance PrettyPrint TypeArg where
 printText0(TypeArg v e k _) = case k of Comma -> printText0 v <> comma
					 _ -> printText0 v <+> colon 
					      <+> printText0 e

instance PrettyPrint Variance where 
    printText0 CoVar = text plusS
    printText0 ContraVar = text minusS
    printText0 InVar = empty

instance PrettyPrint ExtClass where 
    printText0(ExtClass c v _) = printText0 c <> printText0 v

instance PrettyPrint ProdClass where 
    printText0(ProdClass l _) = hcat $ punctuate (text timesS) 
			       (map printText0 l)

instance PrettyPrint Kind where 
    printText0(Kind l c _) = (hcat $ punctuate (text funS) 
				  (map printText0 l))
				 <> text funS 
				 <> printText0 c

instance PrettyPrint Class where 
    printText0(Universe _) = text typeS
    printText0(ClassName n) = printText0 n
    printText0(Downset t) = braces $ text lessS <+> printText0 t
    printText0(Intersection c _) = parens $ commas c 

instance PrettyPrint Types where
    printText0(Types l _) = Pretty.brackets $ commas l

instance PrettyPrint InstOpName where
    printText0 (InstOpName n l) = printText0 n <> hcat(map printText0 l)

