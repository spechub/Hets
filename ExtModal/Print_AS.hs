{- |
Module      :  $Header$
Copyright   :  DFKI GmbH 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

printing AS_ExtModal ExtModalSign data types
-}

module ExtModal.Print_AS where

import Common.Keywords
import Common.AS_Annotation
import Common.Doc
import Common.DocUtils
import Common.Id
import qualified Common.Lib.MapSet as MapSet

import qualified Data.Map as Map
import qualified Data.Set as Set

import ExtModal.AS_ExtModal
import ExtModal.ExtModalSign
import ExtModal.Keywords

import CASL.AS_Basic_CASL (FORMULA (..))
import CASL.ToDoc

instance Pretty EM_BASIC_ITEM where
        pretty (Simple_mod_decl time id_list ax_list _) = fsep
          [(if time then keyword timeS else empty) <+> keyword modalityS
          , semiAnnos pretty id_list
          , if null ax_list then empty else
                specBraces (semiAnnos pretty ax_list)]
        pretty (Nominal_decl id_list _) = sep
          [ keyword nominalS, semiAnnos pretty id_list ]

modPrec :: MODALITY -> Int
modPrec m = case m of
  Simple_modality _ -> 0 -- strongest
  Guard _ -> 1
  TransitiveClosure _ -> 2
  Composition _ _ -> 3
  Union _ _ -> 4 -- weakest

printMPrec :: Bool -> MODALITY -> MODALITY -> Doc
printMPrec b oP cP =
  (if (if b then (>) else (>=)) (modPrec oP) $ modPrec cP then id else parens)
  $ pretty cP

instance Pretty MODALITY where
        pretty mdl = case mdl of
          Simple_modality idt ->
            if tokStr idt == emptyS then empty else pretty idt
          Guard sen -> prJunct sen <> keyword tmGuardS
          TransitiveClosure md -> printMPrec False mdl md
            <> keyword tmTransClosS
          Composition md1 md2 -> printMPrec True mdl md1
            <> keyword tmCompositionS
            <> printMPrec False mdl md2
          Union md1 md2 -> printMPrec True mdl md1
            <> keyword tmUnionS
            <> printMPrec False mdl md2

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

instance FormExtension EM_FORMULA where
  isQuantifierLike ef = case ef of
    UntilSince {} -> False
    _ -> True

isEMJunct :: FORMULA EM_FORMULA -> Bool
isEMJunct f = case f of
  ExtFORMULA (UntilSince {}) -> True
  _ -> isJunct f

prJunct :: FORMULA EM_FORMULA -> Doc
prJunct f = (if isEMJunct f then parens else id) $ pretty f

instance Pretty EM_FORMULA where
  pretty ef = case ef of
    BoxOrDiamond choice modality leq_geq number s _ ->
      let sp = case modality of
                 Simple_modality _ -> (<>)
                 _ -> (<+>)
          mdl = pretty modality
      in sep [ (if choice then brackets mdl else less `sp` mdl `sp` greater)
               <+> if leq_geq && number == 1 then empty else
                keyword (if leq_geq then lessEq else greaterEq)
                <> text (show number)
              , prJunct s]
    Hybrid choice nom s _ ->
      keyword (if choice then atS else hereS) <+> pretty nom
      <+> prJunct s
    UntilSince choice s1 s2 _ -> printInfix True sep (prJunct s1)
      (keyword $ if choice then untilS else sinceS)
      $ prJunct s2
    PathQuantification choice s _ ->
      keyword (if choice then allPathsS else somePathsS) <+> prJunct s
    NextY choice s _ ->
      keyword (if choice then nextS else yesterdayS) <+> prJunct s
    StateQuantification dir_choice choice s _ ->
      keyword (if dir_choice then if choice then generallyS else eventuallyS
               else if choice then hithertoS else previouslyS)
      <+> prJunct s
    FixedPoint choice p_var s _ -> sep
      [ keyword (if choice then muS else nuS) <+> pretty p_var
      , bullet <+> prJunct s]

instance Pretty EModalSign where
        pretty = printEModalSign id

printEModalSign :: (FORMULA EM_FORMULA -> FORMULA EM_FORMULA) -> EModalSign
                -> Doc
printEModalSign sim sign =
        let mds = modalities sign
            tms = time_modalities sign
            nms = nominals sign in
        printSetMap (keyword rigidS <+> keyword opS) empty
            (MapSet.toMap $ rigidOps sign)
        $+$
        printSetMap (keyword rigidS <+> keyword predS) empty
            (MapSet.toMap $ rigidPreds sign)
        $+$
        (if Map.null mds then empty else fsep
          [ keyword modalitiesS
          , sepBySemis (map sidDoc (Map.keys mds))
          , let fs = Map.elems mds in if null $ concat fs then empty else
            specBraces $ printFormulaOfEModalSign sim fs ])
        $+$
        (if Set.null tms then empty else
        keyword timeS <+> keyword modalitiesS
                    <+> sepBySemis (map sidDoc (Set.toList tms)))
        $+$
        (if Set.null nms then empty else
        keyword nominalsS <+> sepBySemis (map sidDoc (Set.toList nms)))

printFormulaOfEModalSign :: FormExtension f => (FORMULA f -> FORMULA f)
  -> [[Annoted (FORMULA f)]] -> Doc
printFormulaOfEModalSign sim = vcat . map
  (sepBySemis . map (printAnnoted $ pretty . sim))
