
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
import AsToLe
import PrettyPrint
import Pretty
import FiniteMap
import Keywords
import GlobalAnnotations

noPrint :: Bool -> Doc -> Doc
noPrint b d = if b then empty else d

instance PrettyPrint Le.ClassItem where
    printText0 ga (Le.ClassItem _ sups defn@(Intersection defns _) insts _) =
	(noPrint (null sups)
	   (ptext lessS <+> if null $ tail sups 
	    then printText0 ga $ head sups
	    else parens (commas ga sups))
	<> noPrint (null sups || null defns) space
	<> noPrint (null defns)
	   (ptext equalS <+> printText0 ga defn)
	) $$ noPrint (null insts) 
             (ptext "Instances" $$ 
	      vcat (map (printText0 ga) insts))
    printText0 _ _ = error "PrintLe.printText0 for Le.ClassItem"

printList0 :: (PrettyPrint a) => GlobalAnnos -> [a] -> Doc
printList0 ga l = noPrint (null l)
		      (if null $ tail l then printText0 ga $ head l
		       else parens $ commas ga l)

instance (PrettyPrint a, Ord a, PrettyPrint b) 
    => PrettyPrint (FiniteMap a b) where
    printText0 ga m =
	let l = fmToList m in
	    vcat(map (\ (a, b) -> printText0 ga a <+> ptext "->"
		 <+> printText0 ga b) l)

instance PrettyPrint [Kind] where
    printText0 = printList0

instance PrettyPrint [TypeScheme] where
    printText0 = printList0

instance PrettyPrint Env where
    printText0 ga e = printText0 ga (classEnv e)
	$$ ptext "Type Constructors"
	$$ printText0 ga (typeKinds e)
	$$ ptext "Assumptions"
        $$ printText0 ga (assumps e)  
	$$ vcat (map (printText ga) (reverse $ envDiags e))

{-
showEnv e = showMap ((++) . tokStr) showClassItem (classEnv e) .
	    showString "\nType Constructors\n" .
	    showMap showId (showSepList (showString ", ") showKind)
		    (typeKinds e) .
	    showString "\nAssumptions\n" .
	    showMap showId (showSepList (showString ", ") showScheme) 
		    (assumps e) .
	    showChar '\n' .
	    showList (reverse $ envDiags e)
-}
