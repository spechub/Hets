
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

instance PrettyPrint ClassInfo where
    printText0 ga (ClassInfo _ sups defn insts) =
	(noPrint (isNothing defn)
	   (ptext equalS <+> printText0 ga defn)
	<> noPrint (null sups || isNothing defn) space
	<> noPrint (null sups)
	   (ptext lessS <+> if null $ tail sups 
	    then printText0 ga $ head sups
	    else parens (commas ga sups))
	) $$ noPrint (null insts) 
             (ptext "Instances" $$ 
	      vcat (map (printText0 ga) insts))

printList0 :: (PrettyPrint a) => GlobalAnnos -> [a] -> Doc
printList0 ga l = noPrint (null l)
		      (if null $ tail l then printText0 ga $ head l
		       else parens $ commas ga l)

instance (PrettyPrint a, Ord a, PrettyPrint b) 
    => PrettyPrint (FiniteMap a b) where
    printText0 ga m =
	let l = fmToList m in
	    vcat(map (\ (a, b) -> printText0 ga a <+> printText0 ga b) l)

instance PrettyPrint [Kind] where
    printText0 ga l = colon <+> printList0 ga l

instance PrettyPrint [TypeScheme] where
    printText0 ga l = colon <+> printList0 ga l

instance PrettyPrint [ClassId] where
    printText0 ga l = colon <+> printList0 ga l

instance PrettyPrint a => PrettyPrint (Maybe a) where
    printText0 _ Nothing = empty
    printText0 ga (Just c) =  printText0 ga c

instance PrettyPrint Env where
    printText0 ga e = printText0 ga (classMap e)
	$$ ptext "Type Constructors"
	$$ printText0 ga (typeKinds e)
        $$ ptext "Type Variables" <+> printText0 ga (typeVars e)
	$$ ptext "Assumptions"
        $$ printText0 ga (assumps e)  
	$$ vcat (map (printText ga) (reverse $ envDiags e))

