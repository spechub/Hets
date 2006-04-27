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
import Common.PrettyPrint
import Common.PPUtils
import Common.AS_Annotation
import Common.Doc 
import CASL.Print_AS_Basic
import CASL.Sign
import Modal.AS_Modal
import Modal.ModalSign
import CASL.AS_Basic_CASL (FORMULA(..))
import CASL.ToDoc

printFormulaOfModalSign :: Pretty f => [[Annoted (FORMULA f)]] -> Doc
printFormulaOfModalSign f =
    vcat $ map rekuPF f
        where rekuPF :: Pretty f => [Annoted (FORMULA f)] -> Doc
              rekuPF tf = fsep $ punctuate semi
                          $ map (printAnnoted pretty) tf

instance PrettyPrint M_BASIC_ITEM where
    printText0 ga = Common.Doc.toText ga . pretty

instance Pretty M_BASIC_ITEM where
    pretty (Simple_mod_decl is fs _) =
        cat [keyword modalityS <+> semiAnnos pretty is
            , specBraces $ semiAnnos pretty fs]
    pretty (Term_mod_decl ss fs _) =
        cat [keyword termS <+> keyword modalityS <+> semiAnnos pretty ss
            , specBraces $ semiAnnos pretty fs]

instance PrettyPrint RIGOR where
    printText0 = CASL.Print_AS_Basic.toText

instance Pretty RIGOR where
    pretty Rigid = keyword rigidS
    pretty Flexible = keyword flexibleS

instance PrettyPrint M_SIG_ITEM where
    printText0 = CASL.Print_AS_Basic.toText

instance Pretty M_SIG_ITEM where
    pretty (Rigid_op_items r ls _) =
        pretty r <+> keyword (opS ++ pluralS ls) <+>
             semiAnnos pretty ls
    pretty (Rigid_pred_items r ls _) =
        pretty r <+> keyword (predS ++ pluralS ls) <+>
             semiAnnos pretty ls

instance PrettyPrint M_FORMULA where
    printText0 = CASL.Print_AS_Basic.toText

instance Pretty M_FORMULA where
    pretty (BoxOrDiamond b t f _) =
        let sp = case t of
                         Simple_mod _ -> (<>)
                         _ -> (<+>)
            td = pretty t
            fd = condParensInnerF (printFormula pretty) parens f
        in if b then brackets td <> fd
           else less `sp` td `sp` greater <+> fd

instance PrettyPrint MODALITY where
    printText0 = CASL.Print_AS_Basic.toText

instance Pretty MODALITY where
    pretty (Simple_mod ident) =
        if tokStr ident == emptyS then empty
           else pretty ident
    pretty (Term_mod t) = pretty t

instance PrettyPrint ModalSign where
    printText0 = CASL.Print_AS_Basic.toText

instance Pretty ModalSign where
    pretty = printModalSign

printModalSign :: ModalSign -> Doc
printModalSign s = 
    let ms = modies s
        tms = termModies s in
    printSetMap (keyword rigidS <+> keyword opS) empty (rigidOps s)      
    $+$ 
    printSetMap (keyword rigidS <+> keyword predS) space (rigidPreds s)
    $+$ (if Map.null ms then empty else
        cat [keyword modalitiesS <+> (fsep $ punctuate semi $ 
            map sidDoc (Map.keys ms))
            , specBraces (printFormulaOfModalSign $ Map.elems ms)])
    $+$ (if Map.null tms then empty else
        cat [keyword termS <+> keyword modalityS <+> (fsep $ punctuate semi $
                map idDoc (Map.keys tms))
            , specBraces (printFormulaOfModalSign $ Map.elems tms)])
    
condParensInnerF :: Pretty f => (FORMULA f -> Doc)
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
