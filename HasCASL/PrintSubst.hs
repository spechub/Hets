{- |
Module      :  $Header$
Description :  pretty printing substitutions
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  experimental
Portability :  portable

pretty printing substitutions
-}

module HasCASL.PrintSubst where


import HasCASL.Subst

import HasCASL.As()
import HasCASL.PrintAs()

import Common.Doc
import Common.DocUtils

import qualified Data.Map as Map


instance Pretty SubstConst where
    pretty (SConst i _) = pretty i

instance Pretty a => Pretty (SRule a) where
    pretty (Blocked x) = mapsto <+> pretty x <+> parens (text "BLOCKED")
    pretty (Ready x) = mapsto <+> pretty x

instance Pretty Subst where
    pretty (Subst (a,b,_)) =
        vcat [ text "Substitution", text $ replicate 70 '='
             , prettyRuleMap "Termmap" a, prettyRuleMap "Typemap" b]

prettyRuleMap :: (Pretty key, Pretty val)
                 => String -> Map.Map key (SRule val) -> Doc
prettyRuleMap t m | Map.null m = empty
                  | otherwise =
                      vcat $ (if null t then [] else 
                                  [ text t <+> colon
                                  , text $ map (const '-') [0..length t+1]])
                               ++ map prettyRule (Map.toList m)

prettyRule :: (Pretty key, Pretty val) => (key, SRule val) -> Doc
prettyRule (k, v) = pretty k <+> pretty v

