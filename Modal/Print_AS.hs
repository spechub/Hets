{- |
Module      :  $Header$
Copyright   :  (c) Wiebke Herding, C. Maeder, Uni Bremen 2004-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
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
import Common.GlobalAnnotations
import Common.AS_Annotation
import CASL.Print_AS_Basic
import CASL.Sign
import Modal.AS_Modal
import Modal.ModalSign
import CASL.AS_Basic_CASL (FORMULA(..))

printFormulaOfModalSign :: PrettyPrint f => GlobalAnnos
                        -> [[Annoted (FORMULA f)]] -> Doc
printFormulaOfModalSign ga f =
    vcat $ map rekuPF f
        where rekuPF ::PrettyPrint f =>  [Annoted (FORMULA f)] -> Doc
              rekuPF tf = fsep $ punctuate semi
                          $ map (printAnnotedFormula_Text0 ga False) tf

instance PrettyPrint M_BASIC_ITEM where
    printText0 ga (Simple_mod_decl is fs _) =
        text modalityS <+> semiAnno_text ga is
              <> braces (semiAnno_text ga fs)
    printText0 ga (Term_mod_decl ss fs _) =
        text termS <+> text modalityS <+> semiAnno_text ga  ss
              <> braces (semiAnno_text ga fs)

instance PrettyPrint RIGOR where
    printText0 _ Rigid = text rigidS
    printText0 _ Flexible = text flexibleS

instance PrettyPrint M_SIG_ITEM where
    printText0 ga (Rigid_op_items r ls _) =
        hang (printText0 ga r <+> text (opS ++ pluralS ls)) 4 $
             semiAnno_text ga ls
    printText0 ga (Rigid_pred_items r ls _) =
        hang (printText0 ga r <+> text (predS ++ pluralS ls)) 4 $
             semiAnno_text ga ls

instance PrettyPrint M_FORMULA where
    printText0 ga (BoxOrDiamond b t f _) =
        let sp = case t of
                         Simple_mod _ -> (<>)
                         _ -> (<+>)
            td = printText0 ga t
            fd = condParensInnerF (printFORMULA ga) parens f
        in if b then brackets td <> fd
           else text lessS `sp` td `sp` text greaterS <+> fd

instance PrettyPrint MODALITY where
    printText0 ga (Simple_mod ident) =
        if tokStr ident == emptyS then empty
           else printText0 ga ident
    printText0 ga (Term_mod t) = printText0 ga t

instance PrettyPrint ModalSign where
    printText0 ga s =
        let ms = modies s
            tms = termModies s in       -- Map Id [Annoted (FORMULA M_FORMULA)]
        printSetMap (text rigidS <+> text opS) empty ga (rigidOps s)
        $$
        printSetMap (text rigidS <+> text predS) space ga (rigidPreds s)
        $$ (if Map.null ms then empty else
        text modalitiesS <+> semiT_text ga (Map.keys ms)
            <> braces (printFormulaOfModalSign ga $ Map.elems ms))
        $$ (if Map.null tms then empty else
        text termS <+> text modalityS <+> semiT_text ga (Map.keys tms)
            <> braces (printFormulaOfModalSign ga (Map.elems tms)))



condParensInnerF :: PrettyPrint f => (FORMULA f -> Doc)
                    -> (Doc -> Doc)    -- ^ a function that surrounds
                                       -- the given Doc with appropiate
                                       -- parens
                    -> FORMULA f -> Doc
condParensInnerF pf parens_fun f =
    case f of
    Quantification _ _ _ _ -> f'
    True_atom _            -> f'
    False_atom _           -> f'
    Predication _ _ _      -> f'
    Definedness _ _        -> f'
    Existl_equation _ _ _  -> f'
    Strong_equation _ _ _  -> f'
    Membership _ _ _       -> f'
    _                      -> parens_fun f'
    where f' = pf f
