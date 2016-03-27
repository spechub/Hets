{- |
Module      :  ./ExtModal/Print_AS.hs
Copyright   :  DFKI GmbH 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

printing AS_ExtModal ExtModalSign data types
-}

module ExtModal.Print_AS where

import Common.Keywords
import Common.Doc
import Common.DocUtils
import Common.Id
import qualified Common.Lib.MapSet as MapSet

import qualified Data.Set as Set

import ExtModal.AS_ExtModal
import ExtModal.ExtModalSign
import ExtModal.Keywords

import CASL.AS_Basic_CASL (FORMULA (..))
import CASL.ToDoc

instance Pretty ModDefn where
  pretty (ModDefn time term id_list ax_list _) = fsep
          [(if time then keyword timeS else empty)
           <+> (if term then keyword termS else empty)
           <+> keyword modalityS
          , semiAnnos pretty id_list
          , if null ax_list then empty else
                specBraces (vcat $ map pretty ax_list)]

instance Pretty FrameForm where
  pretty (FrameForm l f _) = case f of
        [] -> topSigKey (varS ++ pluralS l) <+> printVarDecls l
        [s] | null l -> pretty s
        _ | null l -> printAnnotedBulletFormulas f
        _ -> fsep [fsep $ forallDoc : printVarDeclL l
                  , printAnnotedBulletFormulas f]

instance Pretty EM_BASIC_ITEM where
  pretty itm = case itm of
    ModItem md -> pretty md
    Nominal_decl id_list _ -> sep [keyword nominalS, semiAnnos pretty id_list]

modPrec :: MODALITY -> Int
modPrec m = case m of
  SimpleMod _ -> 0 -- strongest
  TermMod _ -> 0 -- strongest
  Guard _ -> 1
  TransClos _ -> 2
  ModOp Composition _ _ -> 3
  ModOp Intersection _ _ -> 4
  ModOp Union _ _ -> 5
  ModOp OrElse _ _ -> 6 -- weakest

printMPrec :: Bool -> MODALITY -> MODALITY -> Doc
printMPrec b oP cP =
  (if (if b then (>) else (>=)) (modPrec oP) $ modPrec cP then id else parens)
  $ pretty cP

instance Pretty MODALITY where
        pretty mdl = case mdl of
          SimpleMod idt ->
            if tokStr idt == emptyS then empty else pretty idt
          TermMod t -> pretty t
          Guard sen -> prJunct sen <> keyword quMark
          TransClos md -> printMPrec False mdl md
            <> keyword tmTransClosS
          ModOp o md1 md2 -> fsep [printMPrec True mdl md1
            , keyword (show o) <+> printMPrec False mdl md2]

prettyRigor :: Bool -> Doc
prettyRigor b = keyword $ if b then rigidS else flexibleS

instance Pretty EM_SIG_ITEM where
        pretty (Rigid_op_items rig op_list _) =
                fsep [prettyRigor rig <+> keyword (opS ++ pluralS op_list),
                     semiAnnos pretty op_list]
        pretty (Rigid_pred_items rig pred_list _) =
                fsep [prettyRigor rig <+> keyword (predS ++ pluralS pred_list),
                     semiAnnos pretty pred_list]

instance FormExtension EM_FORMULA where
  isQuantifierLike ef = case ef of
    UntilSince {} -> False
    PrefixForm _ f _ -> isQuant f
    _ -> True
  prefixExt ef = case ef of
    ModForm _ -> id
    _ -> (bullet <+>)

isEMJunct :: FORMULA EM_FORMULA -> Bool
isEMJunct f = case f of
  ExtFORMULA (UntilSince {}) -> True
  _ -> isJunct f

prJunct :: FORMULA EM_FORMULA -> Doc
prJunct f = (if isEMJunct f then parens else id) $ pretty f

instance Pretty FormPrefix where
  pretty fp = case fp of
    BoxOrDiamond choice modality gEq number ->
      let sp = case modality of
                 SimpleMod _ -> (<>)
                 _ -> (<+>)
          mdl = pretty modality
      in (case choice of
                  Box -> brackets mdl
                  Diamond -> less `sp` mdl `sp` greater
                  EBox -> text oB <> mdl <> text cB)
               <+> if gEq && number == 1 then empty else
                (if gEq then empty else keyword lessEq)
                <> text (show number)
    Hybrid choice nom ->
      keyword (if choice then atS else hereS) <+> pretty nom
    PathQuantification choice ->
      keyword (if choice then allPathsS else somePathsS)
    NextY choice ->
      keyword (if choice then nextS else yesterdayS)
    StateQuantification dir_choice choice ->
      keyword (if dir_choice then if choice then generallyS else eventuallyS
               else if choice then hithertoS else previouslyS)
    FixedPoint choice p_var ->
      keyword (if choice then muS else nuS) <+> pretty p_var <+> bullet

instance Pretty EM_FORMULA where
  pretty ef = case ef of
    PrefixForm p s _ -> (case p of
      BoxOrDiamond _ m _ _ -> case m of
        SimpleMod _ -> hsep
        _ -> sep
      _ -> hsep) [pretty p, prJunct s]
    UntilSince choice s1 s2 _ -> printInfix True sep (prJunct s1)
      (keyword $ if choice then untilS else sinceS)
      $ prJunct s2
    ModForm md -> pretty md

instance Pretty EModalSign where
    pretty sign =
        let mds = modalities sign
            tims = timeMods sign
            terms = termMods sign
            nms = nominals sign in
        printSetMap (keyword flexibleS <+> keyword opS) empty
            (MapSet.toMap $ flexOps sign)
        $+$
        printSetMap (keyword flexibleS <+> keyword predS) space
            (MapSet.toMap $ flexPreds sign)
        $+$
        vcat (map (\ i -> fsep
          $ [keyword timeS | Set.member i tims]
          ++ [keyword termS | Set.member i terms]
          ++ [keyword modalityS, idDoc i])
            $ Set.toList mds)
        $+$
        (if Set.null nms then empty else
        keyword nominalS <+> sepBySemis (map idDoc (Set.toList nms)))
