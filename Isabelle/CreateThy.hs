{- |
Module      :  $Header$
Copyright   :  (c) C. Maeder, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

dumping a LibEnv to Isabelle theory files
-}

module Isabelle.CreateThy where

import Data.List

import Common.AS_Annotation
import Common.PrettyPrint
import Common.PPUtils
import Common.Lib.Pretty as P
import Common.ProofUtils

import Isabelle.IsaSign as IsaSign
import Isabelle.Translate
import Isabelle.IsaPrint

printIsaTheory :: String -> String -> Sign -> [Named Sentence] -> Doc
printIsaTheory tn libdir sign sens = let
    b = baseSig sign
    bs = showBaseSig b
    ld = if null libdir then "" else libdir ++ "/Isabelle/"
    use = if null ld then empty else text "uses" <+>
           doubleQuotes (text $ ld ++ "prelude")
    in text ("theory " ++ tn)
    $$ text "imports" <+> (if case b of
                          Main_thy -> False
                          HOLCF_thy -> False
                          _ -> True then doubleQuotes
                                    $ text $ ld ++ bs else text bs)
    $$ use
    $$ text "begin"
    $++$ printTheoryBody sign sens
    $++$ text "end"

printTheoryBody :: Sign -> [Named Sentence] -> Doc
printTheoryBody sig sens =
    let (axs, rest) = getAxioms (prepareSenNames transString sens)
        (defs, rs) = getDefs rest
        (rdefs, ts) = getRecDefs rs
        tNames = map senName $ ts ++ axs
    in
    callML "initialize" (text $ show $ map Quote tNames) $++$
    printText sig $++$
    (if null axs then empty else text "axioms" $$
        vsep (map printNamedSen axs)) $++$
    (if null defs then empty else text "defs" $$
        vsep (map printNamedSen defs)) $++$
    (if null rdefs then empty else
        vsep (map printNamedSen rdefs)) $++$
    (if null ts then empty else
        vsep (map ( \ t -> printNamedSen t $$
                   text (case sentence t of
                         Sentence { thmProof = Just s } -> s
                         _ -> "oops")
                  $++$ callML "record" (text $ show $ Quote $ senName t)) ts))

callML :: String -> Doc -> Doc
callML fun args =
    text "ML" <+> doubleQuotes (text ("Header." ++ fun) <+> args)

data QuotedString = Quote String
instance Show QuotedString where
    show (Quote s) = init . tail . show $ show s

getAxioms, getDefs, getRecDefs :: [Named Sentence] ->
                 ([Named Sentence], [Named Sentence])

getAxioms = partition ( \ s -> case sentence s of
                            Sentence {} -> isAxiom s 
                            _ -> False)

getDefs = partition ( \ s -> case sentence s of
                            ConstDef {} -> True
                            _ -> False)

getRecDefs = partition ( \ s -> case sentence s of
                            RecDef {} -> True
                            _ -> False)
