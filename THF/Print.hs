{- |
Module      :  $Header$
Description :  A collection of data-structures and functions. e.g SingTHF, SymbolTHF
Copyright   :  (c) A. Tsogias, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Alexis.Tsogias@dfki.de
Stability   :  provisional
Portability :  portable

Data structures and functions used in Logic_THF and HasCASL2THF
-}

module THF.Print where

import Common.DocUtils
import Common.Doc
import Common.AS_Annotation

import THF.As
import THF.Cons
import THF.PrintTHF

import qualified Data.Map as Map
-- import qualified Data.Set as Set

instance Pretty BasicSpecTHF where
    pretty (BasicSpecTHF _ a) = printTPTPTHF a

instance Pretty THFFormula where
    pretty = printTHF

instance Pretty Include where
    pretty = printTHF

instance Pretty TPTP_THF where
    pretty = printTHF

instance Pretty THFTypedConst where
    pretty = printTHF

instance Pretty AtomicWord where
    pretty = printTHF

instance Pretty SymbolTHF where
  pretty s = (text "Name: ") <+> printTHF (symName s)
        <+> text (" Type: " ++ (drop 3 (show $ symType s)))

instance Pretty SignTHF where
    pretty s =
        let ts = foldl (\d (i, k) -> d $+$ (printTHF i <+> text ":" <+> pretty k))
                    empty (Map.toList $ types s)
            cs = foldl (\d (i, k) -> d $+$ (printTHF i <+> text ":" <+> pretty k))
                    empty (Map.toList $ consts s)
           -- ss  = foldl (\d k -> d $+$ (pretty k)) empty (Set.toList $ symbols s)
        in text "Types: " $+$ ts $++$ text "Constatns: " $+$ cs

instance Pretty Kind where
    pretty k = case k of
        TType           -> text "$tType"
        FunKind k1 k2 _ -> pretty k1  <+> text "->" <+> pretty k2
        Const c         -> printTHF c
        SysType st      -> printSystemType st

instance Pretty TypeInfo where
    -- pretty ti = pretty typeKind
    pretty ti = text "Name:" <+> (printTHF $ typeName ti) <+>
                text "Kind:" <+> (pretty $ typeKind ti) <+>
                text "Def:" <+> (pretty $ typeDef ti)

instance Pretty ConstInfo where
    -- pretty ci = pretty constKind
    pretty ci = text "Name:" <+> (printTHF $ constName ci) <+>
                text "Kind:" <+> (pretty $ constKind ci) <+>
                text "Def:" <+> (pretty $ constDef ci)

printProblemTHF :: SignTHF -> [Named SentenceTHF] -> Named SentenceTHF -> Doc
printProblemTHF sig ax goal = text "Signature:" $+$ pretty sig
    $++$ text "Axioms:" $+$
            (foldl (\d e -> d $+$  printNamedSentenceTHF e) empty ax)
    $++$ text "Goal:" $+$ printNamedSentenceTHF goal

printNamedSentenceTHF :: Named SentenceTHF -> Doc
printNamedSentenceTHF ns = (text (senAttr ns)) <+> text ":"
        <+> (pretty $ sentence ns)

