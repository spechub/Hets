{-| 
Module      :  $Header$
Copyright   :  (c) C. Maeder, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  paolot@tzi.de
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
    use s = if null ld then empty else text ("use" ++ s) <+> 
           doubleQuotes (text $ ld ++ "prelude")
    in text ("theory " ++ tn) 
    $$ text "imports" <+> (if case b of
                          Main_thy -> False
                          HOLCF_thy -> False
                          _ -> True then doubleQuotes 
                                    $ text $ ld ++ bs else text bs)
    $$ use "s" 
    $$ text "begin"
    $$ use ""
    $++$ printTheoryBody sign sens
    $++$ text "end"

printTheoryBody :: Sign -> [Named Sentence] -> Doc
printTheoryBody sig sens =
    let (axs, rest) = getAxioms (prepareSenNames transString sens)
        (defs, rs) = getDefs rest
        (rdefs, ts) = getRecDefs rs
    in 
    printText sig $++$
    (if null axs then empty else text "axioms" $$ 
        vsep (map printNamedSen axs)) $++$
    (if null defs then empty else text "defs" $$
        vsep (map printNamedSen defs)) $++$
    (if null rdefs then empty else 
        vsep (map printNamedSen rdefs)) $++$
    (if null ts then empty else
        vsep (map ( \ t -> printNamedSen t $$ text "oops") ts))

getAxioms, getDefs, getRecDefs :: [Named Sentence] -> 
                 ([Named Sentence], [Named Sentence])

getAxioms = partition ( \ s -> case sentence s of 
                            Sentence _ -> True
                            _ -> False)

getDefs = partition ( \ s -> case sentence s of 
                            ConstDef _ -> True
                            _ -> False)

getRecDefs = partition ( \ s -> case sentence s of 
                            RecDef _ _ -> True
                            _ -> False)

