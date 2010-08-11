{- |
Module      :  $Header$
Description :  pretty printing ADL syntax
Copyright   :  (c) Stef Joosten, Christian Maeder DFKI GmbH 2010
License     :  GPLv2 or higher

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

-}

module Adl.Print (adlGA) where

import Adl.As
import Common.AS_Annotation
import Common.Doc
import Common.DocUtils
import Common.GlobalAnnotations
import Common.Id

import Data.List
import qualified Data.Map as Map

instance Pretty Concept where
  pretty c = case c of
    C s -> pretty s
    _ -> text $ show c

instance Pretty Relation where
  pretty (Sgn n c1 c2) =
    (if tokStr n `elem` ["I", "V"] then keyword (tokStr n) else pretty n)
    <> case (c1, c2) of
      (Anything, Anything) -> empty
      _ | c1 == c2 -> brackets $ pretty c1
      _ -> brackets $ hcat [pretty c1, cross, pretty c2]

pOp :: UnOp -> Id
pOp o = case o of
  Co -> converseId
  Cp -> minusId
  _ -> stringToId $ show o

instance Pretty UnOp where
  pretty = idDoc . stringToId . show

inOp :: MulOp -> Id
inOp = stringToId . show

instance Pretty MulOp where
  pretty o = let i = idDoc (inOp o) in case o of
    Fc -> i
    Fd -> i
    _ -> space <> i <> space

prettyParen :: (Expression -> Bool) -> Expression -> Doc
prettyParen p e = (if p e then parens else id) $ pretty e

minusId :: Id
minusId = mkId [mkSimpleId $ show Cp, placeTok]

converseId :: Id
converseId = mkId [placeTok, mkSimpleId $ show Co]

displayMap :: DisplayMap
displayMap = Map.fromList $ map ( \ (i, l) -> (i, Map.singleton DF_LATEX l))
  [ (minusId, [mkSimpleId "\\overline{", placeTok, mkSimpleId "}"])
  , (converseId, [mkSimpleId "\\widetilde{", placeTok, mkSimpleId "}"])
  , (inOp Fi, [mkSimpleId "\\cap"])
  , (inOp Fu, [mkSimpleId "\\cup"])
  , (inOp Fd, [mkSimpleId "\\dag"])
  , (inOp Ri, [mkSimpleId "\\vdash"])
  , (inOp Rr, [mkSimpleId "\\dashv"])
  , (stringToId $ show Co, [mkSimpleId "{^\\smile}"])
  , (pOp K0, [mkSimpleId "\\texttt{*}"])
  , (pOp K1, [mkSimpleId "\\texttt{+}"])
  ]

adlGA :: GlobalAnnos
adlGA = emptyGlobalAnnos
  { display_annos = displayMap }

instance Pretty Expression where
  pretty e = useGlobalAnnos adlGA $ case e of
    Tm r -> pretty r
    MulExp o es ->
      fcat . punctuate (pretty o) $ map
        (prettyParen (\ a -> case a of
           MulExp p _ -> p >= o || o == Rr && p == Ri
           _ -> False)) es
    UnExp o r -> (if o >= Cp
                  then idApplDoc (pOp o) . (: [])
                  else (<> pretty o))
      $ prettyParen (\ a -> case a of
        MulExp _ _ -> True
        UnExp p _ -> o /= Cp && p == Cp
        _ -> False) r

instance Pretty Prop where
  pretty = text . showUp

instance Pretty RangedProp where
  pretty = pretty . propProp

instance Pretty Object where
  pretty (Object n e as os) = sep
    [ fsep [pretty n <> colon, case e of
          MulExp Re _ -> parens
          _ -> id
        $ pretty e]
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
    Plug p o -> sep [keyword $ showUp p, pretty o]
    Population b r l -> let d = prettyContent l in
      if b then equals <+> d <> dot else fsep
        [ keyword "POPULATION"
        , pretty r
        , keyword "CONTAINS"
        , d ]

instance Pretty Context where
  pretty (Context m ps) = let l = vcat $ map pretty ps in case m of
    Nothing -> l
    Just t -> vcat
      [keyword "CONTEXT" <+> pretty t, l, keyword "ENDCONTEXT"]
