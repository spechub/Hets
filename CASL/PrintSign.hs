
{- HetCATS/CASL/PrintSign.hs
   $Id$
   Authors: Christian Maeder
            Carsten Fischer
   Year:    2003
   
   printing Sign

-}

module CASL.PrintSign where

import Common.Keywords
import Common.Lib.Pretty
import qualified Common.Lib.Map as Map
import Common.PrettyPrint
import Common.PPUtils
import Common.GlobalAnnotations

import CASL.Sign

instance PrettyPrint OpType where
         printText0 ga (OpType{opKind = oK, opArgs = oA, opRes = oR})
	      | null oA   = printPartial
                            <+> printText0 ga oR
	      | otherwise = crossT_text ga oA
			    <+> text funS 
			    <>  printPartial
			    <+> printText0 ga oR
	      where
              printPartial = noPrint (oK==Partial) (text quMark) 

instance PrettyPrint SymbType where
	 printText0 ga (OpAsItemType ot) = printText0 ga ot
	 printText0 ga (PredType pt)    = printList0 ga (space<>text timesS) pt
         printText0 _ Sort              = text sortS

instance PrettyPrint Symbol where
         printText0 ga (Symbol{symbId = sI, symbType = sT}) 
             = printText0 ga sI <+> colon <+> printText0 ga sT

instance PrettyPrint Component where
	 printText0 ga (Component mId opT _) 
             = (case mId of
		Just i -> printText0 ga i <+> colon
		_      -> empty)
               <+> printText0 ga opT

instance PrettyPrint Alternative where
         printText0 ga (Construct i ot compLs _) 
	     = ptext typeS <> printText0 ga i <+> ptext equalS 
	       <+> printText0 ga ot
	       <+> if null compLs then empty 
                   else parens $ semiT_text ga compLs 
	                <+> if (opKind ot == Partial) then space<>ptext quMark
	                   else empty 
         printText0 ga (Subsort sId _) = printText0 ga sId

instance PrettyPrint GenKind where
         printText0 _ Free      = ptext freeS <> space
         printText0 _ Generated = ptext generatedS <> space
         printText0 _ Loose     = empty
        
instance PrettyPrint VarDecl where
         printText0 ga (VarDecl{varId=vI, varSort=vS}) 
             = printText0 ga vI <+> colon <+> printText0 ga vS

instance PrettyPrint SortDefn where
         printText0 ga (SubsortDefn vd form _) 
             = braces $ printText0 ga vd <+> ptext "." <+> printText0 ga form 
         printText0 ga (Datatype annAltLs _ genIt _) 
             = printList0 ga (space <> ptext barS <> space) annAltLs 
	       $$ printText0 ga (GenItems genIt []) 

instance PrettyPrint SortItem where
         printText0 ga (SortItem{sortId=sI,sortRels=sR,sortDef=mSD}) 
             = ptext sortS <+> printText0 ga sI 
	       $$ printSI (supersorts sR)  (char '<')
               $$ printSI (subsorts sR) (char '>')
	       $$ printSI (allsupersrts sR) (text $ "<*") 
               $$ printSI (allsubsrts sR)   (text $ ">*") 
	       $$ case mSD of
		       Just sorDef -> 
		            case sorDef of
		               SubsortDefn _ _ _ -> 
		                   ptext sortS <+> printText0 ga sI 
		                   <+> ptext equalS <+> printText0 ga sorDef
		               Datatype _ genK _ _ ->
		                   printText0 ga genK <> ptext typeS 
                                   <+> printText0 ga sI <+> ptext defnS
                                   <+> printText0 ga sorDef
		       _ -> empty
               where
               printSI xs doc 
                   = noPrint (null xs) (ptext sortS <+> printText0 ga sI <+> 
					doc <+> commaT_text ga xs)

instance PrettyPrint BinOpAttr where
	 printText0 _ Assoc = ptext assocS
	 printText0 _ Comm  = ptext commS
	 printText0 _ Idem  = ptext idemS

instance PrettyPrint OpAttr where
         printText0 ga (BinOpAttr binOp) = printText0 ga binOp
         printText0 ga (UnitOpAttr term) = ptext unitS <+> printText0 ga term 

instance PrettyPrint OpDefn where
         printText0 ga (OpDef vDecLs anTerm _) 
             = parens (semiT_text ga vDecLs) <> colon
       	       <+> printText0 ga anTerm 
         printText0 ga (Constr symbol) = printText0 ga symbol
         printText0 ga (Select symboLs symbol)
	     = printText0 ga symbol <+> parens (commaT_text ga symboLs)

instance PrettyPrint OpItem where
         printText0 ga (OpItem{opId=i,opType=oT,opAttrs=oAtLs,opDefn=mODef}) 
	     = ptext opS <+> printText0 ga i <+>
	       (case mODef of
		  Nothing  -> colon <+> printText0 ga oT
		                 <+> noPrint (null oAtLs) comma
	                         <+> printList0 ga comma oAtLs
		  Just d   -> printText0 ga d)

instance PrettyPrint PredDefn where
         printText0 ga (PredDef vDecLs form _) 
             = parens $ semiT_text ga vDecLs <+> text equivS 
	       <+> printText0 ga form 

instance PrettyPrint PredItem where
         printText0 ga (PredItem{predId=pI, predType=pType, 
				 predDefn=mPrDef}) 
			= printText0 ga pI<+>colon
                          <+> crossT_text ga pType
			  $$ case mPrDef of
				Just preDef -> printText0 ga pI 
					       <+> printText0 ga preDef
				Nothing     -> empty

instance PrettyPrint TypeQualifier where
         printText0 _ OfType = colon
         printText0 _ AsType = ptext asS

instance PrettyPrint Term where
         printText0 ga (VarId i sId qual _) 
             = parens (case qual of 
			 Explicit -> ptext varS 
			 _        -> ptext ("%" ++ varS)
	       <+> printText0 ga i <+> colon 
	       <+> printText0 ga sId)

         printText0 ga (OpAppl _i opT termLs _qual _) 
             = parens (text opS <+> printText0 ga opT) 
               <> parens (commaT_text ga termLs) 
         printText0 ga (Typed term tQual sId _) 
             = printText0 ga term <+> printText0 ga tQual 
	       <+> printText0 ga sId
         printText0 ga (Cond t1 form t2 _)
             = printText0 ga t1 <+> text whenS 
	       <+> printText0 ga form 
	       <+> text elseS <+> printText0 ga t2

instance PrettyPrint Quantifier where
         printText0 _ Forall = ptext forallS
         printText0 _ Exists = ptext existsS
	 printText0 _ ExistsUnique = ptext (existsS++exMark)

instance PrettyPrint LogOp where
         printText0 _ NotOp   = ptext notS
         printText0 _ AndOp   = ptext lAnd
         printText0 _ OrOp    = ptext lOr
         printText0 _ ImplOp  = ptext implS
         printText0 _ EquivOp = ptext equivS
         printText0 _ IfOp    = ptext ifS

instance PrettyPrint PolyOp where
         printText0 _ DefOp     = ptext defS
         printText0 _ EqualOp   = ptext equalS
         printText0 _ ExEqualOp = ptext exEqual

instance PrettyPrint Formula where
 	 printText0 ga (Quantified quan vdLs form _) 
              = hang (printText0 ga quan 
 	             <+> semiT_text ga vdLs) 4 (char '.') 
                <+> printText0 ga form
 	 printText0 ga (Connect logOp formLs _) 
              = printList0 ga (printText0 ga logOp<>space) formLs 
	 printText0 ga (TermTest polyOp termLs _)
	     = printList0 ga (printText0 ga polyOp<>space) termLs
         printText0 ga (PredAppl i pT termLs _qual _)
              = parens (text predS <+> printText0 ga i <+> colon 
                        <+> crossT_text ga pT)
                <+> parens (commaT_text ga termLs)
         printText0 ga (ElemTest term sId _) 
 	     = printText0 ga term <+> text inS <+> printText0 ga sId
         printText0 _ (TrueAtom _)  = ptext trueS
         printText0 _ (FalseAtom _) = ptext falseS
         printText0 ga (AnnFormula anForm) = printText0 ga anForm

instance PrettyPrint SigItem where
         printText0 ga (ASortItem annSoIt)  = printText0 ga annSoIt 
         printText0 ga (AnOpItem annOpIt)   = printText0 ga annOpIt 
         printText0 ga (APredItem annPrIt)  = printText0 ga annPrIt 

instance PrettyPrint Sign where
         printText0 ga sAsMap 
             = let l = Map.toList (getMap sAsMap) in
	       vcat (map (\ (_,b)-> commaT_text ga b) l)

instance PrettyPrint RawSymbol where
         printText0 ga (ASymbol symbol)    = printText0 ga symbol
         printText0 ga (AnID i)            = printText0 ga i
         printText0 ga (AKindedId kind i) 
	     = printText0 ga kind <+> colon <+> printText0 ga i

instance PrettyPrint Kind where
         printText0 _ SortKind = ptext sortS 
         printText0 _ FunKind  = empty 
         printText0 _ PredKind = ptext predS 
        
instance PrettyPrint Axiom where
         printText0 ga (AxiomDecl vDecLs form _ ) 
             = text forallS <+> parens (semiT_text ga vDecLs) 
	       <+> char '.' <+> printText0 ga form

instance PrettyPrint Sentence where
         printText0 ga (Axiom annAx) = printText0 ga annAx
         printText0 ga (GenItems genIt _ ) 
	     = text generatedS <+> braces (commaT_text ga genIt)

-- Helpfunctions
-- | Makes a Doc from Lists; intersperses a Seperator;
printList0::PrettyPrint a=>GlobalAnnos->Doc->[a]->Doc
printList0 ga s l  
    = listSep_text s ga l
