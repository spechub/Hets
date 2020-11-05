{- |
Module      :  ./THF/Print.hs
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
import THF.As (THFFormula, FormulaRole (..))

import qualified Data.HashMap.Lazy as Map
import Data.Maybe (fromMaybe)

{- -----------------------------------------------------------------------------
Some pretty instances for datastructures defined in Cons and Sign and
other print methods
----------------------------------------------------------------------------- -}

instance Pretty BasicSpecTHF where
    pretty (BasicSpecTHF a) = printTPTPTHF a

instance Pretty SymbolTHF where
    pretty s = case symType s of
        ST_Const t -> pretty (symId s) <+> text ":" <+> pretty t
        ST_Type k -> pretty (symId s) <+> text ":" <+> pretty k

instance Pretty SignTHF where
    pretty s =
        let ts = Map.foldr (\ ti d -> d $+$ pretty ti) empty (types s)
            cs = Map.foldr (\ ci d -> d $+$ pretty ci) empty (consts s)
        in text "%Types:" $+$ ts $++$ text "%Constants: " $+$ cs

instance Pretty Kind where
    pretty k = case k of
        Kind -> text "$tType"

instance Pretty Type where
    pretty t = case t of
        TType -> text "$tType"
        OType -> text "$o"
        IType -> text "$i"
        MapType t1 t2 -> pretty t1 <+> text ">" <+> pretty t2
        CType c -> prettyConstant c
        SType st -> prettyAtomicSystemWord st
        VType v -> prettyUpperWord v
        ParType t1 -> parens $ pretty t1
        ProdType ts -> parens $ sepBy (map pretty ts) starSign

instance Pretty TypeInfo where
    pretty ti = text "thf" <> parens (pretty (typeName ti) <> comma
            <+> text "type" <> comma <+>
                (pretty (typeId ti) <+> colon <+> pretty (typeKind ti))
            <> pretty (typeAnno ti))
            <> text "."

instance Pretty ConstInfo where
    pretty ci = text "thf" <> parens (pretty (constName ci) <> comma
            <+> text "type" <> comma <+>
                (pretty (constId ci) <+> colon <+> pretty (constType ci))
                <> pretty (constAnno ci))
            <> text "."

-- print the signature, with axioms and the proof goal
printProblemTHF :: SignTHF -> [Named THFFormula] -> Named THFFormula -> Doc
printProblemTHF sig ax gl = pretty sig $++$ text "%Axioms:" $+$
    foldl (\ d e -> d $+$ printNamedSentenceTHF (Just Axiom) e) empty ax $++$
    text "%Goal:" $+$ printNamedSentenceTHF (Just Conjecture) gl

-- print a Named Sentence
printNamedSentenceTHF :: Maybe FormulaRole -> Named THFFormula -> Doc
printNamedSentenceTHF r' f =
 let r = fromMaybe (if isAxiom f then Axiom
                    else Conjecture) r'
 in text "thf" <> parens (text (senAttr f) <> comma
     <+> pretty r <> comma <+> pretty (sentence f))
     <> text "."
