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
  pretty c = text $ case c of
    C s -> s
    _ -> show c

instance Pretty Relation where
  pretty (Sgn n c1 c2) =
    text n <> case (c1, c2) of
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

instance Pretty Object where
  pretty (Object n e as os) = sep
    [ fsep [text n <> colon, pretty e]
    , if null as then empty else fsep $ keyword "ALWAYS" : map pretty as
    , if null os then empty else equals <+> brackets (ppWithCommas os) ]

instance Pretty PatElem where
  pretty e = case e of
    Pr r -> pretty r
    Pg c1 c2 -> fsep [keyword "GEN", pretty c1, keyword "ISA", pretty c2]
    Pm ps (Sgn n c1 c2) ->
      let f = elem Uni ps && elem Tot ps
          ns = if f then delete Tot $ delete Uni ps else ps
      in fsep
      [ text n, text "::", pretty c1
      , if f then funArrow else cross, pretty c2
      , if null ns then empty else brackets $ ppWithCommas ns]
      <> dot
    Service o -> sep [keyword "SERVICE", pretty o]
    Ignored -> empty
