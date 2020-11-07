{- |
Module      :  ./Hybrid/Print_AS.hs
Copyright   :  (c) Renato Neves
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  nevrenato@gmail.com
Stability   :  provisional
Portability :  portable

printing Hybrid data types
-}

module Hybrid.Print_AS where

import CASL.AS_Basic_CASL (FORMULA (..))
import CASL.ToDoc

import Common.AS_Annotation
import Common.Doc
import Common.DocUtils
import Common.Id
import Common.Keywords
import qualified Common.Lib.MapSet as MapSet

import Hybrid.AS_Hybrid
import Hybrid.HybridSign
import Hybrid.Keywords
import qualified Data.HashMap.Strict as Map


printFormulaOfHybridSign :: FormExtension f => (FORMULA f -> FORMULA f)
                        -> [[Annoted (FORMULA f)]] -> Doc
printFormulaOfHybridSign sim = semiAnnos (pretty . sim) . concat

instance Pretty H_BASIC_ITEM where
    pretty (Simple_mod_decl is fs _) =
        cat [keyword modalityS <+> semiAnnos pretty is
            , space <> specBraces (semiAnnos pretty fs)]
    pretty (Term_mod_decl ss fs _) =
        cat [keyword termS <+> keyword modalityS <+> semiAnnos pretty ss
            , space <> specBraces (semiAnnos pretty fs)]
    pretty (Simple_nom_decl is fs _) =
        cat [keyword nominalS <+> semiAnnos pretty is
            , space <> specBraces (semiAnnos pretty fs)]

instance Pretty RIGOR where
    pretty Rigid = keyword rigidS
    pretty Flexible = keyword flexibleS

instance Pretty H_SIG_ITEM where
    pretty (Rigid_op_items r ls _) =
        cat [pretty r <+> keyword (opS ++ pluralS ls),
             space <> semiAnnos pretty ls]
    pretty (Rigid_pred_items r ls _) =
        cat [pretty r <+> keyword (predS ++ pluralS ls),
             space <> semiAnnos pretty ls]

instance Pretty H_FORMULA where
    pretty (BoxOrDiamond b t f _) =
        let sp = case t of
                         Simple_mod _ -> (<>)
                         _ -> (<+>)
            td = pretty t
        in sep $ (if b then brackets td
                  else less `sp` td `sp` greater)
               : [condParensInnerF printFormula parens f]
    pretty (At n f _) =
        let sp = (<>)
            td = pretty n
        in sep $ (prettyAt `sp` td) : [condParensInnerF printFormula parens f]
    pretty (Univ n f _) =
        let sp = (<+>)
            td = pretty n
        in sep $ (prettyUniv `sp` td) : [condParensInnerF printFormula parens f]
    pretty (Exist n f _) =
        let sp = (<+>)
            td = pretty n
        in sep $ (prettyExist `sp` td) :
                  [condParensInnerF printFormula parens f]
    pretty (Here n _) =
        let sp = (<+>)
            td = pretty n
        in sep [prettyHere `sp` td]

instance FormExtension H_FORMULA where
  isQuantifierLike _ = False

instance Pretty MODALITY where
    pretty (Simple_mod ident) =
        if tokStr ident == emptyS then empty
           else pretty ident
    pretty (Term_mod t) = pretty t

instance Pretty NOMINAL where
    pretty (Simple_nom i) =
        if tokStr i == emptyS then empty
           else pretty i

instance Pretty HybridSign where
    pretty = printHybridSign id

printHybridSign :: (FORMULA H_FORMULA -> FORMULA H_FORMULA) -> HybridSign -> Doc
printHybridSign sim s =
    let ms = modies s
        tms = termModies s
        ns = nomies s in
    printSetMap (keyword rigidS <+> keyword opS) empty
                (MapSet.toMap $ rigidOps s)
    $+$ printSetMap (keyword rigidS <+> keyword predS) space
        (MapSet.toMap $ rigidPreds s)
    $+$ (if Map.null ms then empty else
        cat [keyword modalitiesS <+> sepBySemis (map sidDoc $ Map.keys ms)
            , specBraces (printFormulaOfHybridSign sim $ Map.elems ms)])
    $+$ (if Map.null tms then empty else
        cat [keyword termS <+> keyword modalityS <+> sepBySemis
                (map idDoc $ Map.keys tms)
            , specBraces (printFormulaOfHybridSign sim $ Map.elems tms)])
    $+$ (if Map.null ns then empty else
        cat [keyword nominalsS <+> sepBySemis (map sidDoc $ Map.keys ns)
            , specBraces (printFormulaOfHybridSign sim $ Map.elems ns)])

condParensInnerF :: Pretty f => (FORMULA f -> Doc)
                    -> (Doc -> Doc)    {- ^ a function that surrounds
                                       the given Doc with appropiate parens -}
                    -> FORMULA f -> Doc
condParensInnerF pf parens_fun f =
    case f of
    Quantification {} -> f'
    Atom {} -> f'
    Predication {} -> f'
    Definedness {} -> f'
    Membership {} -> f'
    ExtFORMULA _ -> f'
    _ -> parens_fun f'
    where f' = pf f
