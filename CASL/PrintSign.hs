module CASL.PrintSign where

-- debugging
--import Data.List (mapAccumL)
--import Data.Char (isDigit)
import Data.Maybe (isJust,fromJust)

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
	      | otherwise = crossT printText0 ga oA
			    <+> text funS 
			    <>  printPartial
			    <+> printText0 ga oR
	      where
              printPartial = if oK==Partial 
			     then text quMark
			     else empty

instance PrettyPrint SymbType where
	 printText0 ga (OpAsItemType ot) = printText0 ga ot
	 printText0 ga (PredType pt) = if null pt then empty
				       else crossT printText0 ga pt
         printText0 ga Sort          = text sortS

instance PrettyPrint Symbol where
         printText0 ga (Symbol{symbId = sI, symbType = sT}) 
             = printText0 ga sI <> colon <> printText0 ga sT

instance PrettyPrint Component where
	 printText0 ga (Component mId opT _) 
             = (case mId of
		Just i -> printText0 ga i <+> colon
		_ -> empty)
               <+> printText0 ga opT

-- noch einmal Christian fragen.
-- er hat was aufgeschrieben: type s = c:tc (comp;..;comp)
instance PrettyPrint Alternative where
         printText0 ga (Construct id ot compLs _) 
	     = ptext typeS <> printText0 ga id <+> ptext equalS 
	       <+> printText0 ga ot
	       <+> if null compLs then empty 
                   else parens $ semiT printText0 ga compLs 
	                <> if (opKind ot == Partial) then space<>ptext quMark
	                   else empty 
         printText0 ga (Subsort sId _) 
	     = printText0 ga sId

instance PrettyPrint GenKind where
         printText0 ga Free      = ptext freeS
         printText0 ga Generated = ptext generatedS
         printText0 ga Loose     = empty
        
instance PrettyPrint VarDecl where
         printText0 ga (VarDecl{varId=vI, varSort=vS}) 
             = printText0 ga vI <+> colon <+> printText0 ga vS

instance PrettyPrint SortDefn where
         printText0 ga (SubsortDefn vd form _) 
             = braces $ printText0 ga vd <+> ptext "." <+> printText0 ga form 
         printText0 ga (Datatype annAltLs genK genIt _) 
             = noPrint (null annAltLs) $
	       printText0 ga genK 
		    <+> commaT printText0 ga genIt 
		    <+> text defnS 
		    <>  vcat (punctuate (text (barS++" ")) 
                               (map (printText0 ga) annAltLs))

-- sortPos und altSorts habe ich noch nicht eingebaut!!
instance PrettyPrint SortItem where
         printText0 ga (SortItem{sortId=sI,sortRels=sR,sortDef=mSD}) 
             = ptext sortS <+> printText0 ga sI 
	       $$ printSI (supersorts sR)  (char '<')
               $$ printSI (subsorts sR) (char '>')
	       $$ printSI (allsupersrts sR) (text $ "<"++timesS) 
               $$ printSI (allsubsrts sR)   (text $ ">"++timesS) 
	       $$ if isJust mSD 
		  then printText0 ga sI 
			   <+> printText0 ga (fromJust mSD) 
		  else empty
               where
               printSI xs doc = if null xs then empty 
                                else printText0 ga sI <+> doc 
                                     <+> commaT printText0  ga xs 
                                     <> comma

instance PrettyPrint BinOpAttr where
	 printText0 ga Assoc = ptext assocS
	 printText0 ga Comm  = ptext commS
	 printText0 ga Idem  = ptext idemS

instance PrettyPrint OpAttr where
         printText0 ga (BinOpAttr binOp) = empty -- ???
         printText0 ga (UnitOpAttr term) = printText0 ga term 

instance PrettyPrint OpDefn where
         printText0 ga (OpDef vDecLs anTerm _) 
             = parens (semiT printText0 ga vDecLs) <> colon
	      <+> printText0 ga anTerm 
         printText0 ga (Constr symbol) = printText0 ga symbol
         printText0 ga (Select symboLs symbol) = printText0 ga symbol
	   <> parens (commaT printText0 ga symboLs)
 
-- ist die Ausgabe richtig?
instance PrettyPrint PredDefn where
         printText0 ga (PredDef vDecLs form _) 
             = parens $ semiT printText0 ga vDecLs <+> text equivS 
	       <+> printText0 ga form 

instance PrettyPrint PredItem where
         printText0 ga (PredItem{predId=pI, predType=pType, 
				 predDefn=mPrDef}) 
			= printText0 ga pI<+>colon
                          <+> crossT printText0 ga pType
			  $$ if isJust mPrDef 
			     then printText0 ga pI 
				  <+> printText0 ga (fromJust mPrDef)
			     else empty

instance PrettyPrint TypeQualifier where
         printText0 ga OfType = colon
         printText0 ga AsType = ptext asS

instance PrettyPrint Term where
         printText0 ga (VarId id sId qual _) 
             = parens ((case qual of 
			Explicit -> ptext varS 
			_        -> ptext ("%" ++ varS))
	                            <+> printText0 ga id <> colon 
		                    <> printText0 ga sId)

         printText0 ga (OpAppl id opType termLs qual _) 
             = parens (text opS <+> printText0 ga opType) 
               <> parens (commaT printText0 ga termLs) 
         printText0 ga (Typed term tQual sId _) 
             = printText0 ga term <+> printText0 ga tQual 
	       <+> printText0 ga sId
         printText0 ga (Cond t1 form t2 _)
             = printText0 ga t1 <+> text whenS 
	       <+> printText0 ga form 
	       <+> text elseS <+> printText0 ga t2

instance PrettyPrint Quantifier where
         printText0 ga Forall = ptext forallS
         printText0 ga Exists = ptext existsS
	 printText0 ga ExistsUnique = ptext (existsS++exMark)

instance PrettyPrint LogOp where
         printText0 ga NotOp   = ptext notS
         printText0 ga AndOp   = ptext lAnd
         printText0 ga OrOp    = ptext lOr
         printText0 ga ImplOp  = ptext implS
         printText0 ga EquivOp = ptext equivS
         printText0 ga IfOp    = ptext ifS

instance PrettyPrint PolyOp where
         printText0 ga DefOp     = ptext defS
         printText0 ga EqualOp   = ptext equalS
         printText0 ga ExEqualOp = ptext exEqual

instance PrettyPrint Formula where
 	 printText0 ga (Quantified quan vdLs form _) 
              = hang (printText0 ga quan 
 	             <+> semiT printText0 ga vdLs) 4 (char '.') 
                <+> printText0 ga form
 	 printText0 ga (Connect logOp formLs _) 
              = sep $ punctuate (printText0 ga logOp<>space) 
                      (makeDocList ga formLs) 
                -- klammern?
 	 printText0 ga (TermTest polyOp termLs _) 
              = sep $ punctuate (printText0 ga polyOp<>space) 
 	             (makeDocList ga termLs) 
                -- klammern?
         printText0 ga (PredAppl id pT termLs qual _)
              = parens (text predS <+> printText0 ga id <> colon 
                                             <> crossT printText0 ga pT)
                <+> parens (commaT printText0 ga termLs)
         printText0 ga (ElemTest term sId _) 
 	     = printText0 ga term <+> text inS <+> printText0 ga sId
         printText0 ga (TrueAtom _)  = ptext trueS
         printText0 ga (FalseAtom _) = ptext falseS
         printText0 ga (AnnFormula anForm) = printText0 ga anForm

-- -- Hilffunktion
makeDocList::PrettyPrint a=>GlobalAnnos->[a]->[Doc]
makeDocList ga l = map (printText0 ga) l



instance PrettyPrint SigItem where
         printText0 ga (ASortItem annSoIt) = printText0 ga annSoIt -- ???
         printText0 ga (AnOpItem annOpIt)   = printText0 ga annOpIt -- ???
         printText0 ga (APredItem annPrIt)  = printText0 ga annPrIt -- ???

instance PrettyPrint OpItem where
    printText0 ga o = printText0 ga (opId o) <+> colon <+>
		      printText0 ga (opType o) -- ...

-- hier muss ich irgendwie mit einer Liste als zweitem Argument umgehen,
-- geht das ueberhaupt??
instance PrettyPrint Sign where
         printText0 ga sAsMap 
             = let l = Map.toList (getMap sAsMap) in
	       vcat (map (\ (_,b)-> commaT printText0 ga b) l)

instance PrettyPrint RawSymbol where
         printText0 ga (ASymbol symbol)    = printText0 ga symbol
         printText0 ga (AnID id)           = printText0 ga id
         printText0 ga (AKindedId kind id) 
	     = printText0 ga kind <> colon <> printText0 ga id

instance PrettyPrint Kind where
         printText0 ga SortKind = ptext sortS -- ???
         printText0 ga FunKind  = empty -- ???
         printText0 ga PredKind = ptext predS -- ???
        
instance PrettyPrint Axiom where
         printText0 ga (AxiomDecl vDecLs form _ ) 
             = text forallS <+> parens (semiT printText0 ga vDecLs) 
	       <+> char '.' <+> printText0 ga form


instance PrettyPrint Sentence where
         printText0 ga (Axiom annAx) = printText0 ga annAx
         printText0 ga (GenItems genIt _ ) 
	     = braces $ commaT printText0 ga genIt
               -- generate/free ???

