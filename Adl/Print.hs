{- |
Module      :  $Header$
Description :  pretty printing ADL syntax
Copyright   :  (c) Stef Joosten, Christian Maeder DFKI GmbH 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

-}

module Adl.Print () where

import Adl.As
import Common.Doc
import Common.DocUtils

import Data.List

instance Pretty Concept where
  pretty c = case c of
    C s -> pretty s
    _ -> text $ show c

instance Pretty Relation where
  pretty (Sgn n c1 c2) =
    pretty n <> case (c1, c2) of
      (Anything, Anything) -> empty
      _ | c1 == c2 -> brackets $ pretty c1
      _ -> brackets $ hcat [pretty c1, cross, pretty c2]

instance Pretty UnOp where
  pretty o = case o of
    K0 -> text "*"
    K1 -> text "+"
    Cp -> text "-" -- prefix!
    Co -> breve

instance Pretty MulOp where
  pretty o = case o of
    Fc -> semi
    Fd -> dagger
    Fi -> space <> andDoc <> space
    Fu -> space <> orDoc <> space

prettyParen :: (Expression -> Bool) -> Expression -> Doc
prettyParen p e = (if p e then parens else id) $ pretty e

instance Pretty Expression where
  pretty e = case e of
    Tm r -> pretty r
    MulExp o es ->
      fcat $ punctuate (pretty o) $ map
        (prettyParen (\ a -> case a of
           MulExp p _ -> p >= o
           _ -> False)) es
    UnExp o r -> hcat $ (if o == Cp then reverse else id)
      [ prettyParen (\ a -> case a of
        MulExp _ _ -> True
        UnExp p _ -> o /= Cp && p == Cp
        _ -> False) r
      , pretty o ]

instance Pretty RuleType where
  pretty t = case t of
    Implication -> vdash
    ReverseImpl -> dashv
    Equivalence -> equals

instance Pretty Rule where
  pretty r = case r of
    Rule e1 t e2 -> hsep [pretty e1, pretty t, pretty e2]
    Truth e -> pretty e

instance Pretty Prop where
  pretty = text . showProp

instance Pretty RangedProp where
  pretty = pretty . propProp

instance Pretty Object where
  pretty (Object n e as os) = sep
    [ fsep [pretty n <> colon, pretty e]
    , if null as then empty else fsep $ keyword "ALWAYS" : map pretty as
    , if null os then empty else equals <+> brackets (ppWithCommas os) ]

instance Pretty RuleKind where
  pretty = keyword . showRuleKind

instance Pretty RuleHeader where
  pretty h = case h of
    Always -> empty
    RuleHeader k t -> keyword
      (if k == SignalOn then "SIGNAL" else "RULE")
      <+> pretty t <+> pretty k

instance Pretty KeyAtt where
  pretty (KeyAtt mt e) = sep [case mt of
      Nothing -> empty
      Just t -> pretty t <> colon
      , pretty e]

instance Pretty KeyDef where
  pretty (KeyDef l c atts) = fsep
    [ keyword "KEY"
    , pretty l <> colon
    , pretty c
    , parens $ ppWithCommas atts ]

instance Pretty Pair where
   pretty (Pair x y) = parens $ ppWithCommas [x, y]

prettyContent :: [Pair] -> Doc
prettyContent = brackets . vcat . punctuate semi . map pretty

instance Pretty PatElem where
  pretty e = case e of
    Pr k r -> pretty k <+> pretty r
    Pg c1 c2 -> fsep [keyword "GEN", pretty c1, keyword "ISA", pretty c2]
    Pk k -> pretty k
    Pm ps (Sgn n c1 c2) b ->
      let u = rProp Uni
          t = rProp Tot
          f = elem u ps && elem t ps
          ns = if f then delete t $ delete u ps else ps
      in fsep
      [ pretty n, text "::", pretty c1
      , if f then funArrow else cross, pretty c2
      , if null ns then empty else brackets $ ppWithCommas ns]
      <> if b then empty else dot
    Service o -> sep [keyword "SERVICE", pretty o]
    Population b r l -> let d = prettyContent l in
      if b then equals <+> d <> dot else fsep
        [ keyword "POPULATION"
        , pretty r
        , keyword "CONTAINS"
        , d ]

instance Pretty Context where
  pretty (Context ps) = vcat $ map pretty ps
