{-
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Wiebke Herding and Uni Bremen 2003
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

  Abstract syntax for modal logic extension of CASL
  Only the added syntax is specified
-}

module Modal.AS_Modal where

import Common.Id
import Common.AS_Annotation 
import Common.GlobalAnnotations
import CASL.AS_Basic_CASL
import Common.Lib.Pretty
import Common.PrettyPrint

-- DrIFT command
{-! global: UpPos !-}

data M_BASIC_SPEC =
     M_Basic_spec [Annoted ModalBasicItems]
		  deriving (Show,Eq)

type ModalBasicItems = BASIC_ITEMS M_BASIC_ITEM () M_FORMULA

data M_BASIC_ITEM =
	         Flexible_Op_items [Annoted (OP_ITEM M_FORMULA)] [Pos]
		 -- pos: op, semi colons
	       | Flexible_Pred_items [Annoted (PRED_ITEM M_FORMULA)] [Pos]
		 -- pos: pred, semi colons
             deriving (Eq, Show)

type ModalFORMULA = FORMULA M_FORMULA

data M_FORMULA = 
	       Box (Either Id (TERM M_FORMULA)) () [Pos]
               -- The identifier and the term specify the kind of the modality
	       -- pos: "[]"	    
	     | Diamond (Either Id (TERM M_FORMULA)) (ModalFORMULA) [Pos]
               -- The identifier and the term specify the kind of the modality
               -- pos: "<>"
             deriving (Eq, Show)

instance PrettyPrint M_FORMULA where
    printText0 ga (Box t f _) = 
       ptext "[" <> pprintModality ga t <+> ptext"]" <+> printText0 ga f
    printText0 ga (Diamond t f _) = 
       ptext "<" <> pprintModality ga t <+> ptext">" <+> printText0 ga f

pprintModality :: GlobalAnnos -> Either Id (TERM M_FORMULA) -> Doc
pprintModality ga (Left ident) = 
  if show ident=="empty" then empty
     else printText0 ga ident
pprintModality ga (Right t) = printText0 ga t
