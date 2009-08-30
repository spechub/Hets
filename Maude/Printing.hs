{- |
Module      :  $Header$
Description :  Translation from Haskell to Maude
Copyright   :  (c) Martin Kuehl, Uni Bremen 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  mkhl@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Translations from Haskell to Maude.

The translations from Haskell datatypes to Maude source code are
implemented as instances of the typeclass 'Pretty' as defined in the
modules "Common.Doc" and "Common.DocUtils", which see.

Nothing else is exported by this module.
-}

module Maude.Printing () where

import Maude.AS_Maude
import Maude.Symbol

import Common.Doc
import Common.DocUtils (Pretty(..))

import Data.List (intersperse)

-- * Combinators

-- | Convert every item in @list@, combine with @dsep@, wrap with @wrap@.
combine :: (Pretty a) => (Doc -> Doc) -> ([Doc] -> Doc) -> [a] -> Doc
combine _ _ [] = empty
combine wrap dsep list = wrap . dsep . map pretty $ list

-- | Separate with spaces, wrap with parentheses.
parenPretties :: (Pretty a) => [a] -> Doc
parenPretties = combine parens hsep

-- | Separate with spaces, wrap with square brackets.
bracketPretties :: (Pretty a) => [a] -> Doc
bracketPretties = combine brackets hsep

-- | Separate with newlines, wrap with square brackets and newlines.
combineHooks :: (Pretty a) => [a] -> Doc
combineHooks = let bracketed doc = lbrack $+$ doc <> rbrack
               in combine bracketed vcat

-- | Assemble a pretty-printing for all parts of a Sentence,
-- distinguishing conditional Sentence from simple ones.
prettySentence :: (Pretty a, Pretty b) =>
    String -> String -> Doc -> a -> b -> [Condition] -> [StmntAttr] -> Doc
prettySentence s1 s2 op t1 t2 cs as = hsep $ if null cs
    then [keyword s1, pretty t1, op, pretty t2, pretty as, dot]
    else [keyword s2, pretty t1, op, pretty t2, pretty cs, pretty as, dot]

-- * Pretty instances

-- ** Pretty Sentences

instance Pretty Membership where
    pretty (Mb t s cs as) = prettySentence "mb" "cmb" colon t s cs as

instance Pretty Equation where
    pretty (Eq t1 t2 cs as) = prettySentence "eq" "ceq" equals t1 t2 cs as

instance Pretty Rule where
    pretty (Rl t1 t2 cs as) = prettySentence "rl" "crl" implies t1 t2 cs as

-- ** Pretty Conditions
instance Pretty Condition where
    pretty cond = let pretty' x y z = hsep [pretty x, y, pretty z]
        in case cond of
            MbCond t  s  -> pretty' t colon s
            EqCond t1 t2 -> pretty' t1 equals t2
            RwCond t1 t2 -> pretty' t1 implies t2
            MatchCond t1 t2 -> pretty' t1 (text ":=") t2
    pretties = combine (text "if" <+>) (hsep . intersperse andDoc)

-- ** Pretty Attributes

instance Pretty Attr where
    pretty attr = case attr of
        Assoc -> text "assoc"
        Comm -> text "comm"
        Idem -> text "idem"
        Iter -> text "iter"
        Id term -> text "id:" <+> pretty term
        LeftId term -> text "id-left:" <+> pretty term
        RightId term -> text "id-right:" <+> pretty term
        Strat ints -> text "strat" <+> parenPretties ints
        Memo -> text "memo"
        Prec int -> text "prec" <+> pretty int
        Gather qids -> text "gather" <+> parenPretties qids
        Format qids -> text "format" <+> parenPretties qids
        Ctor -> text "ctor"
        Config -> text "config"
        Object -> text "object"
        Msg -> text "msg"
        Frozen ints -> text "frozen" <+> parenPretties ints
        Poly ints -> text "poly" <+> parenPretties ints
        Special hooks -> text "special" <+> combineHooks hooks
    pretties = bracketPretties

instance Pretty StmntAttr where
    pretty attr = case attr of
        Owise        -> text "owise"
        Nonexec      -> text "nonexec"
        Metadata str -> text "metadata" <+> doubleQuotes (pretty str)
        Label qid    -> text "label" <+> doubleQuotes (pretty qid)
        Print _      -> empty
    pretties = bracketPretties

-- ** Pretty Hooks

instance Pretty Hook where
    pretty hook = case hook of
        IdHook qid qs -> hsep
            [text "id-hook", pretty qid, parenPretties qs]
        OpHook qid op dom cod -> let symb = mkOpPartial op dom cod
            in hsep [text "op-hook", pretty qid, parens $ pretty symb]
        TermHook qid term -> hsep
            [text "term-hook", pretty qid, parens $ pretty term]
    pretties = combine parens vcat

-- ** Pretty Terms

instance Pretty Term where
    pretty term = case term of
        Const qid _    -> pretty qid
        Var   qid tp   -> hcat [pretty qid, colon, pretty tp]
        Apply qid ts _ -> pretty qid <> (parens . pretty $ ts)
    pretties = combine id sepByCommas

-- ** Pretty Identifiers

instance Pretty Type where
    pretty typ = case typ of
        TypeSort sort -> pretty sort
        TypeKind kind -> pretty kind

instance Pretty Sort where
    pretty (SortId qid) = pretty qid

instance Pretty Kind where
    pretty (KindId qid) = pretty qid

instance Pretty ParamId where
    pretty (ParamId qid) = pretty qid

instance Pretty ViewId where
    pretty (ViewId qid) = pretty qid

instance Pretty ModId where
    pretty (ModId qid) = pretty qid

instance Pretty LabelId where
    pretty (LabelId qid) = pretty qid

instance Pretty OpId where
    pretty (OpId qid) = pretty qid
