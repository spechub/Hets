{- |
Module      :  $Header$
Description :  Transformation between Haskell and Maude
Copyright   :  (c) Adrian Riesco, Facultad de Informatica UCM 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  ariesco@fdi.ucm.es
Stability   :  experimental
Portability :  portable

Translations from Haskell to Maude.
-}

module Maude.Printing () where

import Maude.AS_Maude
import Maude.Symbol

import Data.List (intersperse)

import Common.Doc
import Common.DocUtils (Pretty(..))


combine :: (Pretty a) => (Doc -> Doc) -> ([Doc] -> Doc) -> [a] -> Doc
combine _ _ [] = empty
combine wrap dsep list = wrap . dsep . map pretty $ list

parenPretties :: (Pretty a) => [a] -> Doc
parenPretties = combine parens hsep

bracketPretties :: (Pretty a) => [a] -> Doc
bracketPretties = combine brackets hsep

combineHooks :: (Pretty a) => [a] -> Doc
combineHooks = let bracketed doc = lbrack $+$ doc <> rbrack
    in combine bracketed $ vcat

instance Pretty Membership where
    pretty (Mb t s cs as) = hsep $ if null cs
        then [keyword "mb",  pretty t, colon, pretty s, pretty as, dot]
        else [keyword "cmb", pretty t, colon, pretty s, pretty cs, pretty as, dot]

instance Pretty Equation where
    pretty (Eq t1 t2 cs as) = hsep $ if null cs
        then [keyword "eq",  pretty t1, equals, pretty t2, pretty as, dot]
        else [keyword "ceq", pretty t1, equals, pretty t2, pretty cs, pretty as, dot]

instance Pretty Rule where
    pretty (Rl t1 t2 cs as) = hsep $ if null cs
        then [keyword "rl",  pretty t1, implies, pretty t2, pretty as, dot]
        else [keyword "crl", pretty t1, implies, pretty t2, pretty cs, pretty as, dot]


instance Pretty Condition where
    pretty cond = let pretty' x y z = hsep [pretty x, y, pretty z]
        in case cond of
            MbCond t  s  -> pretty' t colon s
            EqCond t1 t2 -> pretty' t1 equals t2
            RwCond t1 t2 -> pretty' t1 implies t2
            MatchCond t1 t2 -> pretty' t1 (text ":=") t2
    pretties = combine (text "if" <+>) (hsep . intersperse andDoc)


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


instance Pretty Hook where
    pretty hook = case hook of
        IdHook qid qs -> hsep
            [text "id-hook", pretty qid, parenPretties qs]
        OpHook qid op dom cod -> let symb = mkOpPartial op dom cod
            in hsep [text "op-hook", pretty qid, parens $ pretty symb]
        TermHook qid term -> hsep
            [text "term-hook", pretty qid, parens $ pretty term]
    pretties = combine parens vcat


instance Pretty Term where
    pretty term = case term of
        Const qid _    -> pretty qid
        Var   qid tp   -> hcat [pretty qid, colon, pretty tp]
        Apply qid ts _ -> pretty qid <> (parens . pretty $ ts)
    pretties = combine id sepByCommas


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
