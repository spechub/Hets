{- |
Module      :  ./TopHybrid/Print_AS.hs
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  nevrenato@gmail.com
Stability   :  provisional
Portability :  portable

Description :
Instance of class Pretty for hybrid logic
with an arbitrary logic below.
-}

module TopHybrid.Print_AS (printNamedFormula) where

import Common.Doc
import Common.DocUtils
import Common.AS_Annotation
import TopHybrid.AS_TopHybrid
import TopHybrid.TopHybridSign
import Logic.Logic

printNamedFormula :: Named Frm_Wrap -> Doc
printNamedFormula = printAnnoted printFormula . fromLabelledSen

{- the use of the function makeNamed is vacuous, it is only needed
to satisfy the types of the print_named function -}
printFormula :: Frm_Wrap -> Doc
printFormula (Frm_Wrap l f) = case f of
                               UnderLogic f' -> print_named l $ makeNamed "" f'
                               f' -> pretty f'

instance (Pretty f) => Pretty (TH_FORMULA f) where
        pretty (At n f) = keyword "@" <+> pretty n <+> pretty f
        pretty (Uni n f) = keyword "forall worlds" <+> pretty n <+> pretty f
        pretty (Exist n f) = keyword "exist world" <+> pretty n <+> pretty f
        pretty (UnderLogic f) = keyword "{" <+> pretty f <+> keyword "}"
        pretty (Box m f) = keyword "[" <> pretty m <> keyword "]" <+> pretty f
        pretty (Dia m f) = keyword "<" <> pretty m <> keyword ">" <+> pretty f
        pretty (Conjunction f f') = pretty f <+> keyword "/\\" <+> pretty f'
        pretty (Disjunction f f') = pretty f <+> keyword "\\/" <+> pretty f'
        pretty (Implication f f') = pretty f <+> keyword "->" <+> pretty f'
        pretty (BiImplication f f') = pretty f <+> keyword "<->" <+> pretty f'
        pretty (Here n) = pretty n
        pretty (Neg f) = keyword "not" <+> pretty f
        pretty (Par f) = keyword "(" <+> pretty f <+> keyword ")"
        pretty TrueA = keyword "True"
        pretty FalseA = keyword "False"

instance (Pretty s) => Pretty (THybridSign s) where
        pretty x@(THybridSign _ _ s) =
                keyword "Modalities" <+> pretty (modies x) $+$
                keyword "Nominals" <+> pretty (nomies x) $+$
                keyword "Under Sig {" $+$ pretty s $+$ keyword "}"

instance (Pretty b) => Pretty (TH_BSPEC b) where
        pretty (Bspec x b) = pretty x
                                $+$ keyword "Under Spec {" $+$
                                pretty b
                                $+$ keyword "}"

instance Pretty (TH_BASIC_ITEM) where
        pretty (Simple_mod_decl x) = keyword "Modalities" <+> pretty x
        pretty (Simple_nom_decl x) = keyword "Nominals" <+> pretty x

instance Pretty Frm_Wrap where
        pretty (Frm_Wrap _ f) = pretty f
instance Pretty Spc_Wrap where
        pretty (Spc_Wrap _ b f) = pretty b $+$ pretty f
instance Pretty Mor where
        pretty _ = error "Not implemented!"

instance Pretty Sgn_Wrap where
        pretty (Sgn_Wrap _ s) = pretty s
        pretty (EmptySign) = pretty ()
