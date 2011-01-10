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

import HasCASL.As
import HasCASL.Le
import HasCASL.PrintAs()
import HasCASL.SimplifyTerm

import Common.Doc
import Common.DocUtils

import qualified Data.Map as Map

class PrettyInEnv a where
    prettyInEnv :: Env -> a -> Doc

-- instance Pretty a => PrettyInEnv a where
--     prettyInEnv _ x  = pretty x


instance Pretty SubstConst where
    pretty (SConst i _) = pretty i

instance Pretty a => Pretty (SRule a) where
    pretty (Blocked x) = mapsto <+> pretty x <+> parens (text "BLOCKED")
    pretty (Ready x) = mapsto <+> pretty x

instance Pretty Subst where
    pretty (Subst (a,b,_)) =
        text "Subs"
                 <> vcat [ text "titution"
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


instance PrettyInEnv Term where
    prettyInEnv e t = pretty $ simplifyTerm e t

instance PrettyInEnv Type where
    prettyInEnv = const pretty

instance PrettyInEnv a => PrettyInEnv (SRule a) where
    prettyInEnv e (Blocked x) = mapsto <+> prettyInEnv e x <+> parens (text "BLOCKED")
    prettyInEnv e (Ready x) = mapsto <+> prettyInEnv e x

instance PrettyInEnv Subst where
    prettyInEnv e (Subst (a,b,_)) =
        text "Subs"
                 <> vcat [ text "titution"
                         , prettyInEnvRuleMap e "Termmap" a
                         , prettyInEnvRuleMap e "Typemap" b]

prettyInEnvRuleMap :: (Pretty key, PrettyInEnv val)
                 => Env -> String -> Map.Map key (SRule val) -> Doc
prettyInEnvRuleMap e t m | Map.null m = empty
                         | otherwise =
                             vcat $ (if null t then [] else 
                                         [ text t <+> colon
                                         , text $ map (const '-') [0..length t+1]])
                                      ++ map (prettyInEnvRule e) (Map.toList m)

prettyInEnvRule :: (Pretty key, PrettyInEnv val) => Env -> (key, SRule val) -> Doc
prettyInEnvRule e (k, v) = pretty k <+> prettyInEnv e v


prettyTermMapping :: Env -> [(Term, Term)] -> Doc
prettyTermMapping e l = vcat $ map f l where
    f (t1, t2) = prettyInEnv e t1 <+> text "=" <+> prettyInEnv e t2
