
{- HetCATS/HasCASL/PrintLe.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   printing Le data types
-}

module PrintLe where

import As
import PrintAs
import Le
import Maybe
import PrettyPrint
import Pretty
import FiniteMap
import Keywords
import GlobalAnnotations

noPrint :: Bool -> Doc -> Doc
noPrint b d = if b then empty else d

printList0 :: (PrettyPrint a) => GlobalAnnos -> [a] -> Doc
printList0 ga l = noPrint (null l)
		      (if null $ tail l then printText0 ga $ head l
		       else parens $ commas ga l)

instance PrettyPrint ClassInfo where
    printText0 ga (ClassInfo sups defn) =
	noPrint (isNothing defn)
	   (ptext equalS <+> printText0 ga defn)
	<> noPrint (null sups || isNothing defn) space
	<> noPrint (null sups)
	   (ptext lessS <+> printList0 ga sups)

instance PrettyPrint TypeDefn where
    printText0 _ NoTypeDefn = empty
    printText0 _ TypeVarDefn = ptext varS
    printText0 ga (AliasTypeDefn s) = printText ga s
    printText0 ga (SubTypeDefn v t f) =  braces (printText0 ga v 
					   <+> colon
					   <+> printText0 ga t 
					   <+> text dotS
					   <+> printText0 ga f)
    printText0 _ _ = ptext "missing"

instance PrettyPrint TypeInfo where
    printText0 ga (TypeInfo k ks sups defn) =
	colon <> printList0 ga (k:ks) 
	<> noPrint (null sups)
	   (ptext lessS <+> printList0 ga sups)
        <> noPrint (case defn of { NoTypeDefn -> True; _ -> False })
             (space <> ptext equalS <+> printText0 ga defn) 

instance PrettyPrint [Kind] where
    printText0 ga l = colon <> printList0 ga l

instance PrettyPrint [Type] where
    printText0 ga l = colon <> printList0 ga l

instance PrettyPrint [TypeScheme] where
    printText0 ga l = colon <+> printList0 ga l

instance PrettyPrint [ClassId] where
    printText0 ga l = colon <+> printList0 ga l

instance PrettyPrint a => PrettyPrint (Maybe a) where
    printText0 _ Nothing = empty
    printText0 ga (Just c) =  printText0 ga c

instance (PrettyPrint a, Ord a, PrettyPrint b) 
    => PrettyPrint (FiniteMap a b) where
    printText0 ga m =
	let l = fmToList m in
	    vcat(map (\ (a, b) -> printText0 ga a <+> printText0 ga b) l)

instance PrettyPrint Env where
    printText0 ga e = printText0 ga (classMap e)
	$$ ptext "Type Constructors"
	$$ printText0 ga (typeKinds e)
        $$ ptext "Type Variables" <+> printText0 ga (typeVars e)
	$$ ptext "Assumptions"
        $$ printText0 ga (assumps e)  
	$$ vcat (map (printText ga) (reverse $ envDiags e))

