
{- HetCATS/HasCASL/PrintLe.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   printing Le data types
-}

module PrintLe where

import PrintAs
import As
import Le
import AsToLe
import PrettyPrint
import Pretty
import FiniteMap

instance PrettyPrint Le.ClassItem where
    printText0 ga (Le.ClassItem _ sups defn insts _) =
	ptext (showClassList sups [])

instance (PrettyPrint a, Ord a, PrettyPrint b) 
    => PrettyPrint (FiniteMap a b) where
    printText0 ga m =
	let l = fmToList m in
	    vcat(map (\ (a, b) -> printText0 ga a <+> ptext "->"
		 <+> printText0 ga b) l)

instance PrettyPrint Env where
    printText0 ga e = printText0 ga (classEnv e)
	$$ ptext "Type Constructors"
--	$$ printText0 ga (typeKinds e)
	$$ ptext "Assumptions"
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
