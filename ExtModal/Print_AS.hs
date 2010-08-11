{- |
Module      :  $Header$
Copyright   :  DFKI GmbH 2009
License     :  GPLv2 or higher

Maintainer  :  codruta.liliana@gmail.com
Stability   :  experimental
Portability :  portable

printing AS_ExtModal ExtModalSign data types
-}

module ExtModal.Print_AS where

import Common.Keywords
import qualified Data.Map as Map
import qualified Data.Set as Set
import Common.AS_Annotation
import Common.Doc
import Common.DocUtils

import ExtModal.AS_ExtModal
import ExtModal.ExtModalSign
import ExtModal.Keywords
import ExtModal.MorphismExtension

import CASL.AS_Basic_CASL (FORMULA(..))
import CASL.ToDoc

instance Pretty EM_BASIC_ITEM where
        pretty (Simple_mod_decl time id_list ax_list _) =
                cat[if time then (keyword timeS) else empty
                   , keyword modalityS <+> semiAnnos pretty id_list
                   , space <> specBraces (semiAnnos pretty ax_list)]
        pretty (Nominal_decl id_list _) = keyword nominalS <+> semiAnnos pretty id_list

instance Pretty MODALITY where
        pretty (Simple_modality idt) = pretty idt
        pretty (Composition md1 md2) = (keyword tmOParanthS) <> (pretty md1) <>
                                        (keyword tmCompositionS) <> (pretty md2)
                                        <> (keyword tmCParanthS)
        pretty (Union md1 md2) = (keyword tmOParanthS) <> (pretty md1) <> (keyword tmUnionS)
                                 <> (pretty md2) <> (keyword tmCParanthS)
        pretty (TransitiveClosure md) = (keyword tmOParanthS) <> (pretty md) <>
                                        (keyword (tmTransClosS ++ tmCParanthS))
        pretty (Guard sen) = (keyword tmOParanthS) <> (pretty sen) <> (keyword (tmGuardS ++ tmCParanthS))

instance Pretty RIGOR where
        pretty Rigid = keyword rigidS
        pretty Flexible = keyword flexibleS

instance Pretty EM_SIG_ITEM where
        pretty (Rigid_op_items rig op_list _) =
                cat [pretty rig <+> keyword (opS ++ pluralS op_list),
                     space <> semiAnnos pretty op_list]
        pretty (Rigid_pred_items rig pred_list _) =
                cat [pretty rig <+> keyword (predS ++ pluralS pred_list),
                     space <> semiAnnos pretty pred_list]

instance Pretty NOMINAL where
        pretty (Nominal idt) = pretty idt

instance Pretty EM_FORMULA where
        pretty (BoxOrDiamond choice modality leq_geq number em_sentence _) =
                let sp = case modality of
                                Simple_modality _ -> (<>)
                                _ -> (<+>)
                    mdl = pretty modality
                in sep $ (if choice then brackets mdl else less `sp` mdl `sp` greater)
                       : (if leq_geq then keyword lessEq else keyword greaterEq)
                       : (text (show number)) : space : [condParensInnerF (printFormula pretty) parens em_sentence]

        pretty (Hybrid choice nom em_sentence _) =
                sep $ (if choice then keyword atS else keyword hereS) : space : (pretty nom) : space
                    : [condParensInnerF (printFormula pretty) parens em_sentence]
        pretty (UntilSince choice sentence1 sentence2 _) =
                sep $ ([condParensInnerF (printFormula pretty) parens sentence1]
                       ++ ( space : (if choice then keyword untilS else keyword sinceS) : space
                             : [condParensInnerF (printFormula pretty) parens sentence2]))
        pretty (PathQuantification choice em_sentence _) =
                sep $ (if choice then keyword allPathsS else keyword somePathsS) : space
                    : [condParensInnerF (printFormula pretty) parens em_sentence]
        pretty (NextY choice em_sentence _) =
                sep $ (if choice then keyword nextS else keyword yesterdayS) : space
                    : [condParensInnerF (printFormula pretty) parens em_sentence]
        pretty (StateQuantification dir_choice choice em_sentence _) =
                let kw = case dir_choice of
                                True -> if choice then keyword generallyS else keyword eventuallyS
                                _ -> if choice then keyword hithertoS else keyword previouslyS
                in sep $ kw : space : [condParensInnerF (printFormula pretty) parens em_sentence]
        pretty (FixedPoint choice p_var em_sentence _) =
                sep $ (if choice then keyword muS else keyword nuS) : space : (pretty p_var) : space
                        : [condParensInnerF (printFormula pretty) parens em_sentence]

condParensInnerF :: Pretty f => (FORMULA f -> Doc) -> (Doc -> Doc) -> FORMULA f -> Doc
condParensInnerF frm_print parens_fun frm  =
        case frm of
        Quantification _ _ _ _ -> frm'
        True_atom _            -> frm'
        False_atom _           -> frm'
        Predication _ _ _      -> frm'
        Definedness _ _        -> frm'
        Existl_equation _ _ _  -> frm'
        Strong_equation _ _ _  -> frm'
        Membership _ _ _       -> frm'
        ExtFORMULA _           -> frm'
        _                      -> parens_fun frm'
        where frm' = frm_print frm

instance Pretty EModalSign where
        pretty  = printEModalSign id

printEModalSign :: (FORMULA EM_FORMULA -> FORMULA EM_FORMULA) -> EModalSign -> Doc
printEModalSign sim sign =
        let mds = modalities sign
            tms = time_modalities sign
            nms = nominals sign in
        printSetMap (keyword rigidS <+> keyword opS) empty (rigidOps sign)
        $+$
        printSetMap (keyword rigidS <+> keyword predS) empty (rigidPreds sign)
        $+$
        (if Map.null mds then empty else
        cat [keyword modalitiesS <+> (fsep $ punctuate semi $ map sidDoc (Map.keys mds))
            , specBraces (printFormulaOfEModalSign sim $ Map.elems mds)])
        $+$
        (if Set.null tms then empty else
        keyword timeS <+> keyword modalitiesS <+> (fsep $ punctuate semi $ map sidDoc (Set.toList tms)))
        $+$
        (if Set.null nms then empty else
        keyword nominalsS <+> (fsep $ punctuate semi $ map sidDoc (Set.toList nms)))


printFormulaOfEModalSign :: Pretty f => (FORMULA f -> FORMULA f) -> [[Annoted (FORMULA f)]] -> Doc
printFormulaOfEModalSign sim =
        vcat . map (\ tf -> fsep $ punctuate semi $ map (printAnnoted $ pretty . sim) tf)

instance Pretty MorphExtension where
        pretty me = pretty (source me) <+> pretty (target me) <+>
                        text (show (Map.toList (mod_map me))) <+> text (show (Map.toList (nom_map me)))

