{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder  and Uni Bremen 2002-2003

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable

pretty printing a HasCASL environment

-}

module HasCASL.PrintLe where

import HasCASL.As
import HasCASL.HToken
import Common.Id
import HasCASL.PrintAs
import HasCASL.Le
import Data.Maybe
import Common.GlobalAnnotations
import Common.PrettyPrint
import Common.PPUtils
import Common.Lib.Pretty as Pretty
import qualified Common.Lib.Map as Map
import Common.Keywords

instance PrettyPrint ClassInfo where
    printText0 ga (ClassInfo ks) =
	   space <> text lessS <+> printList0 ga ks

printGenKind :: GenKind -> Doc
printGenKind k = case k of
		Loose -> empty
		Free -> text freeS <> space
		Generated -> text generatedS <> space

instance PrettyPrint TypeDefn where
    printText0 _ NoTypeDefn = empty
    printText0 _ PreDatatype = space <> text "%(data type)%"
    printText0 _ TypeVarDefn = space <> text "%(var)%"
    printText0 ga (AliasTypeDefn s) = space <> text assignS 
				      <+> printPseudoType ga s
    printText0 ga (Supertype v t f) = space <> text equalS <+> 
					 braces (printText0 ga v 
					   <+> colon
					   <+> printText0 ga t 
					   <+> text dotS
					   <+> printText0 ga f)
    printText0 ga (DatatypeDefn dd)  = 
	text " %[" <> printText0 ga dd <> text "]%"

instance PrettyPrint AltDefn where
    printText0 ga (Construct i ts p sels) = 
	printText0 ga i <+> colon 
	<+> listSep_text (space<>text funS<>space) ga ts <+>
	    text (case p of 
		   Partial -> funS ++ quMark
		   Total -> funS) <+> text place 
	<+> hcat (map (parens . printText0 ga) sels) 

instance PrettyPrint Selector where
    printText0 ga (Select i t p) = 
	printText0 ga i <+> (case p of 
			     Partial -> text ":?"
			     Total -> colon) <+> printText0 ga t

instance PrettyPrint TypeInfo where
    printText0 ga (TypeInfo _ ks sups defn) =
	space <> colon <+> printList0 ga ks
	<> noPrint (null sups)
	   (space <> text lessS <+> printList0 ga sups)
        <> printText0 ga defn

instance PrettyPrint ConstrInfo where
    printText0 ga (ConstrInfo i t) = 
	printText0 ga i <+> colon <+> printText0 ga t

instance PrettyPrint OpDefn where
    printText0 _ (NoOpDefn b) = space <> text ("%(" ++ show b ++ ")%")
    printText0 _ VarDefn = space <> text "%(var)%"
    printText0 _ (ConstructData i) = space <> text ("%(construct " ++
				     showId i ")%")
    printText0 ga (SelectData c i) = space <> text ("%(select from " ++
				     showId i " constructed by")
				    $$ printList0 ga c <> text ")%"
    printText0 ga (Definition b t) = printText0 ga (NoOpDefn b) <+> 
				     text equalS <+> printText0 ga t
 
instance PrettyPrint OpInfo where
    printText0 ga o = space <> colon <+> printText0 ga (opType o)
		      <> (case opAttrs o of 
			  [] -> empty 
			  l -> comma <> commaT_text ga l)
		      <>  printText0 ga (opDefn o)
 
instance PrettyPrint OpInfos where
    printText0 ga (OpInfos l) = vcat $ map (printText0 ga) l

instance PrettyPrint a => PrettyPrint (Maybe a) where
    printText0 _ Nothing = empty
    printText0 ga (Just c) =  printText0 ga c

instance PrettyPrint DataEntry where 
    printText0 ga (DataEntry im i k args alts) =  
	printGenKind k <> text typeS <+> printText0 ga i 
			 <+> (printList0 ga args 
				       <+> text defnS $$ 
					   vcat (map (printText0 ga) alts))
	$$ nest 2 (if Map.isEmpty im then empty else 
	   text withS <+> text (typeS ++ sS) <+> printText0 ga im)
		       
instance PrettyPrint Sentence where 
    printText0 ga s = case s of
        Formula t -> printText0 ga t
	DatatypeSen ls -> vcat (map (printText0 ga) ls)
        ProgEqSen _ _ pe -> text programS <+> printText0 ga pe
 
instance PrettyPrint Env where
    printText0 ga (Env{classMap=cm, typeMap=tm, 
		       assumps=as, sentences=se, envDiags=ds}) = 
	noPrint (Map.isEmpty cm) (header "Classes")
	$$ printMap0 ga cm
	$$ noPrint (Map.isEmpty tm) (header "Type Constructors")
	$$ printMap0 ga tm
	$$ noPrint (Map.isEmpty as) (header "Assumptions")
        $$ printMap0 ga as
	$$ noPrint (null se) (header "Sentences")
        $$ vcat (map (printText0 ga) se)
	$$ noPrint (null ds) (header "Diagnostics")
	$$ vcat (map (printText0 ga) $ reverse ds)
	where header s =  text "%%" <+> text s 
			  <+> text (replicate (70 - length s) '-')
	      printMap0 :: (PrettyPrint a, Ord a, PrettyPrint b)  
			   => GlobalAnnos -> Map.Map a b -> Doc
	      printMap0 g m =
		  let l = Map.toList m in
			  vcat(map (\ (a, b) -> printText0 g a 
				    <> printText0 g b) l)

instance PrettyPrint SymbolType where
    printText0 ga t = case t of 
      OpAsItemType sc -> printText0 ga sc
      TypeAsItemType k -> printText0 ga k
      ClassAsItemType k -> printText0 ga k

instance PrettyPrint Symbol where
    printText0 ga s = text (case symType s of 
			    OpAsItemType _ -> opS
			    TypeAsItemType _ -> typeS
			    ClassAsItemType _ -> classS) <+> 
                    printText0 ga (symName s) <+> text colonS <+> 
		    printText0 ga (symType s)

instance PrettyPrint RawSymbol where
  printText0 ga rs = case rs of
      AnID i -> printText0 ga i
      AKindedId k i -> printSK k <> printText0 ga i
      AQualId i t -> printSK (symbTypeToKind t) <> printText0 ga i <+> colon 
		       <+> printText0 ga t
