{- |
Module      :  $Header$
Description :  Seveal Pretty instances.
Copyright   :  (c) A. Tsogias, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Alexis.Tsogias@dfki.de
Stability   :  provisional
Portability :  portable

Pretty instances some data structures of As, Sign and Cons
-}

module THF.Print where

import Common.DocUtils
import Common.Doc
import Common.AS_Annotation

import THF.Cons
import THF.Sign
import THF.PrintTHF

import qualified Data.Map as Map

instance Pretty BasicSpecTHF where
    pretty (BasicSpecTHF _ a) = printTPTPTHF a

instance Pretty SymbolTHF where
    pretty s = case symType s of
        ST_Const t  -> text "Constant" <+> pretty (symId s) <+> text ":"
                        <+> pretty t
        ST_Type k   -> text "Type" <+> pretty (symId s) <+> text ":"
                        <+> pretty k

instance Pretty SignTHF where
    pretty s =
        let ts = Map.fold (\ ti d -> d $+$ pretty ti) empty (types s)
            cs = Map.fold (\ ci d -> d $+$ pretty ci) empty (consts s)
        in text "%Types:" $+$ ts $++$ text "%Constants: " $+$ cs

instance Pretty Kind where
    pretty k = case k of
        Kind            -> text "$tType"
        MapKind k1 k2 _ -> pretty k1  <+> text ">" <+> pretty k2
        SysType st      -> prettySystemType st
        ParKind k1      -> parens $ pretty k1

instance Pretty Type where
    pretty t = case t of
        TType           -> text "$tType"
        OType           -> text "$o"
        IType           -> text "$i"
        MapType t1 t2   -> pretty t1 <+> text ">" <+> pretty t2
        CType c         -> prettyConstant c
        SType st        -> prettySystemType st
        ParType t1      -> parens $ pretty t1

instance Pretty TypeInfo where
    pretty ti = text "thf" <> parens (pretty (typeName ti) <> comma
            <+> text "type" <> comma <+> maybe
                (pretty (typeId ti) <+> colon <+> pretty (typeKind ti))
                pretty (typeDef ti) <> pretty (typeAnno ti))
            <> text "."

instance Pretty ConstInfo where
    pretty ci = text "thf" <> parens (pretty (constName ci) <> comma
            <+> text "type" <> comma <+> maybe
                (pretty (constId ci) <+> colon <+> pretty (constType ci))
                pretty (constDef ci) <> pretty (constAnno ci))
            <> text "."

instance Pretty SentenceTHF where
    pretty (Sentence _ f _) = pretty f

printProblemTHF :: SignTHF -> [Named SentenceTHF] -> Named SentenceTHF -> Doc
printProblemTHF sig ax gl = pretty sig $++$ text "%Axioms:" $+$
    foldl (\ d e -> d $+$ printNamedSentenceTHF e) empty ax $++$
    text "%Goal:" $+$ printNamedSentenceTHF gl

printNamedSentenceTHF :: Named SentenceTHF -> Doc
printNamedSentenceTHF ns =
    let (Sentence r f a) = sentence ns
    in text "thf" <> parens (text (senAttr ns) <> comma
            <+> pretty r <> comma <+> pretty f <> pretty a)
        <> text "."
