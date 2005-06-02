{- |
Module      :  $Header$
Copyright   :  (c) Wiebke Herding, C. Maeder, Uni Bremen 2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

  printing AS_Modal ModalSign data types
-}

module COL.Print_AS where

import Common.Id
import Common.Keywords
import qualified Common.Lib.Set as Set
import Common.Lib.Pretty
import Common.PrettyPrint
import Common.PPUtils
import CASL.Print_AS_Basic
import CASL.Sign
import Modal.AS_Modal
import Modal.ModalSign

instance PrettyPrint M_BASIC_ITEM where
    printText0 ga (Simple_mod_decl is fs _) = 
	ptext modalityS <+> semiAnno_text ga is
	      <> braces (semiAnno_text ga fs)
    printText0 ga (Term_mod_decl ss fs _) = 
	ptext termS <+> ptext modalityS <+> semiAnno_text ga ss
	      <> braces (semiAnno_text ga fs)

instance PrettyPrint RIGOR where
    printText0 _ Rigid = ptext rigidS
    printText0 _ Flexible = ptext flexibleS

instance PrettyPrint M_SIG_ITEM where
    printText0 ga (Rigid_op_items r ls _) =
	hang (printText0 ga r <+> ptext opS <> pluralS_doc ls) 4 $ 
	     semiAnno_text ga ls
    printText0 ga (Rigid_pred_items r ls _) =
	hang (printText0 ga r <+> ptext predS <> pluralS_doc ls) 4 $ 
	     semiAnno_text ga ls

instance PrettyPrint M_FORMULA where
    printText0 ga (Box t f _) = 
       brackets (printText0 ga t) <> printText0 ga f
    printText0 ga (Diamond t f _) = 
	let sp = case t of 
			 Simple_mod _ -> (<>)
			 _ -> (<+>)
	    in ptext lessS `sp` printText0 ga t `sp` ptext greaterS 
		   <+> printText0 ga f

instance PrettyPrint MODALITY where
    printText0 ga (Simple_mod ident) = 
	if tokStr ident == emptyS then empty
	   else printText0 ga ident
    printText0 ga (Term_mod t) = printText0 ga t

instance PrettyPrint ModalSign where
    printText0 ga s = 
	let ms = modies s
	    tms = termModies s in 
	printSetMap (ptext rigidS <+> ptext opS) empty ga (rigidOps s)
	$$
	printSetMap (ptext rigidS <+> ptext predS) 
		    space ga (rigidPreds s)
	$$ (if Set.null ms then empty else
	ptext modalitiesS <+> semiT_text ga (Set.toList ms))
	$$ (if Set.null tms then empty else
	ptext termS <+> ptext modalityS <+> semiT_text ga (Set.toList tms))
