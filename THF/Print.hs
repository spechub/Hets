{- |
Module      :  $Header$
Description :  Seveal Pretty instances.
Copyright   :  (c) A. Tsogias, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Alexis.Tsogias@dfki.de
Stability   :  provisional
Portability :  portable

Instances for Pretty for some data structures of As and Cons
-}

module THF.Print where

import Common.DocUtils
import Common.Doc
import Common.AS_Annotation

import THF.As
import THF.Cons
import THF.Sign
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
  pretty s = text "Name: " <+> printTHF (symName s)
        <+> text (" Type: " ++ drop 3 (show $ symType s))

instance Pretty SignTHF where
    pretty s =
        let ts = foldl (\ d (i, k) ->
                            d $+$ (printTHF i <+> text ":" <+> pretty k))
                    empty (Map.toList $ types s)
            cs = foldl (\ d (i, k) ->
                            d $+$ (printTHF i <+> text ":" <+> pretty k))
                    empty (Map.toList $ consts s)
        in text "Types: " $+$ ts $++$ text "Constatns: " $+$ cs

instance Pretty Kind where
    pretty k = case k of
        Kind           -> text "$tType"
        MapKind k1 k2 _ -> pretty k1  <+> text "->" <+> pretty k2
        SysType st      -> printSystemType st

instance Pretty Type where
    pretty t = case t of
        TType           -> text "$tType"
        OType           -> text "$o"
        IType           -> text "$i"
        MapType t1 t2   -> pretty t1 <+> text "->" <+> pretty t2
        CType c         -> printConstant c
        SType st        -> printSystemType st

instance Pretty TypeInfo where
    -- pretty ti = pretty typeKind
    pretty ti = text "Name:" <+> printTHF (typeName ti) <+>
                text "Kind:" <+> pretty (typeKind ti) <+>
                text "Def:" <+> pretty (typeDef ti)

instance Pretty ConstInfo where
    -- pretty ci = pretty constKind
    pretty ci = text "Name:" <+> printTHF (constName ci) <+>
                text "Kind:" <+> pretty (constType ci) <+>
                text "Def:" <+> pretty (constDef ci)

printProblemTHF :: SignTHF -> [Named SentenceTHF] -> Named SentenceTHF -> Doc
printProblemTHF sig ax goal = text "Signature:" $+$ pretty sig
    $++$ text "Axioms:" $+$
            foldl (\ d e -> d $+$  printNamedSentenceTHF e) empty ax
    $++$ text "Goal:" $+$ printNamedSentenceTHF goal

printNamedSentenceTHF :: Named SentenceTHF -> Doc
printNamedSentenceTHF ns = text (senAttr ns) <+> text ":"
                <+> pretty (sentence ns)
