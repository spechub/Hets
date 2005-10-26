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
import Isabelle.IsaHOLCFPrint 

createTheoryText :: Sign -> [Named Sentence] -> Doc
createTheoryText sig sens =
    let (axs, rest) = getAxioms (prepareSenNames transString sens)
        (defs, rs) = getDefs rest
        (rdefs, _) = getRecDefs rs
    in 
    printText sig $++$
    (if null axs then empty else text "axioms" $$ 
        vsep (map printNamedSen axs)) $++$
    (if null defs then empty else text "defs" $$
        vsep (map printNamedSen defs)) $++$
    (if null rdefs then empty else 
        vsep (map printNamedSen rdefs)) 
    $++$ text "end"     

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

printNamedSen :: Named Sentence -> Doc
printNamedSen sen = case s of 
 RecDef kw xs -> text kw $$ fixrecP xs
 _ -> text (case s of
    ConstDef _ -> lab ++ "_def"
    Sentence _ -> lab
    _ -> "theorem " ++ lab) 
    <+> colon <+> doubleQuotes (case senTerm s of
      IsaEq (Const (VName {new=df}) y) t ->  
        text df <+> text "::" <+> printTyp Unquoted y
                 <+> text "==" <+> text (showOUTerm t)
      _ -> printText s)
 where lab = senName sen
       s = sentence sen
       fixrecP as = case as of
              [] -> empty
              [b] -> vcat (map (doubleQuotes . printText) b)
              b:bs -> vcat (map (doubleQuotes . printText) b) 
                      $$ text "and" $++$ fixrecP bs

