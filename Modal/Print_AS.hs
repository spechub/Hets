{- |
Module      :  ./Modal/Print_AS.hs
Copyright   :  (c) Wiebke Herding, C. Maeder, Uni Bremen 2004-2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

printing AS_Modal ModalSign data types
-}

module Modal.Print_AS where

import CASL.AS_Basic_CASL (FORMULA (..))
import CASL.ToDoc

import Common.AS_Annotation
import Common.Doc
import Common.DocUtils
import Common.Id
import Common.Keywords
import qualified Common.Lib.MapSet as MapSet

import Modal.AS_Modal
import Modal.ModalSign

import qualified Data.HashMap.Strict as Map

printFormulaOfModalSign :: FormExtension f => (FORMULA f -> FORMULA f)
                        -> [[Annoted (FORMULA f)]] -> Doc
printFormulaOfModalSign sim = semiAnnos (pretty . sim) . concat

instance Pretty M_BASIC_ITEM where
    pretty (Simple_mod_decl is fs _) =
        cat [keyword modalityS <+> semiAnnos pretty is
            , space <> specBraces (semiAnnos pretty fs)]
    pretty (Term_mod_decl ss fs _) =
        cat [keyword termS <+> keyword modalityS <+> semiAnnos pretty ss
            , space <> specBraces (semiAnnos pretty fs)]

instance Pretty RIGOR where
    pretty Rigid = keyword rigidS
    pretty Flexible = keyword flexibleS

instance Pretty M_SIG_ITEM where
    pretty (Rigid_op_items r ls _) =
        cat [pretty r <+> keyword (opS ++ pluralS ls),
             space <> semiAnnos pretty ls]
    pretty (Rigid_pred_items r ls _) =
        cat [pretty r <+> keyword (predS ++ pluralS ls),
             space <> semiAnnos pretty ls]

instance Pretty M_FORMULA where
    pretty (BoxOrDiamond b t f _) =
        let sp = case t of
                         Simple_mod _ -> (<>)
                         _ -> (<+>)
            td = pretty t
        in sep $ (if b then brackets td
                  else less `sp` td `sp` greater)
               : [condParensInnerF printFormula parens f]

instance FormExtension M_FORMULA where
  isQuantifierLike _ = False

instance Pretty MODALITY where
    pretty (Simple_mod ident) =
        if tokStr ident == emptyS then empty
           else pretty ident
    pretty (Term_mod t) = pretty t

instance Pretty ModalSign where
    pretty = printModalSign id

printModalSign :: (FORMULA M_FORMULA -> FORMULA M_FORMULA) -> ModalSign -> Doc
printModalSign sim s =
    let ms = modies s
        tms = termModies s in
    printSetMap (keyword flexibleS <+> keyword opS) empty
        (MapSet.toMap $ flexOps s)
    $+$ printSetMap (keyword flexibleS <+> keyword predS) space
        (MapSet.toMap $ flexPreds s)
    $+$ (if Map.null ms then empty else
        cat [keyword modalitiesS <+> sepBySemis (map sidDoc $ Map.keys ms)
            , specBraces (printFormulaOfModalSign sim $ Map.elems ms)])
    $+$ (if Map.null tms then empty else
        cat [keyword termS <+> keyword modalityS <+> sepBySemis
                (map idDoc $ Map.keys tms)
            , specBraces (printFormulaOfModalSign sim $ Map.elems tms)])

condParensInnerF :: Pretty f => (FORMULA f -> Doc)
                    -> (Doc -> Doc)    {- ^ a function that surrounds
                                       the given Doc with appropiate parens -}
                    -> FORMULA f -> Doc
condParensInnerF pf parens_fun f =
    case f of
    Quantification {} -> f'
    Atom _ _ -> f'
    Predication {} -> f'
    Definedness _ _ -> f'
    Equation {} -> f'
    Membership {} -> f'
    ExtFORMULA _ -> f'
    _ -> parens_fun f'
    where f' = pf f
