{-
Module      :  $Header$
Copyright   :  (c) Wiebke Herding, C. Maeder, Uni Bremen 2004
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

  printing AS_Modal ModalSign data types
-}

module Modal.Print_AS where

import Common.Id
import Common.Keywords
import qualified Common.Lib.Map as Map
import Common.Lib.Pretty
import Common.PrettyPrint
import Common.PPUtils
import CASL.Print_AS_Basic
import Modal.AS_Modal
import Modal.ModalSign

instance PrettyPrint M_BASIC_ITEM where
    printText0 ga (Simple_mod_decl is _) = 
	ptext modalityS <+> semiAnno_text ga is
    printText0 ga (Term_mod_decl ss _) = 
	ptext termS <+> ptext modalityS <+> semiAnno_text ga ss

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
       ptext "[" <> printText0 ga t <+> ptext"]" <+> printText0 ga f
    printText0 ga (Diamond t f _) = 
       ptext "<" <> printText0 ga t <+> ptext">" <+> printText0 ga f

instance PrettyPrint MODALITY where
    printText0 ga (Simple_mod ident) = 
	if tokStr ident == emptyS then empty
	   else printText0 ga ident
    printText0 ga (Term_mod t) = printText0 ga t

instance PrettyPrint ModalSign where
    printText0 ga s = 
	ptext rigidS <+> ptext opS <+> commaT_text ga (Map.keys $ rigidOps s)
        $$ 	
	ptext rigidS <+> ptext predS 
		  <+> commaT_text ga (Map.keys $ rigidPreds s)
