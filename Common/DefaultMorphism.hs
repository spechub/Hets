{- |
Module      :  $Header$
Copyright   :  (c) C. Maeder, and Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

supply a default morphism for a given signature
-}

-- due to functional deps the instance for Logic.Category cannot be supplied

module Common.DefaultMorphism where

import Common.Lib.Pretty
import Common.LaTeX_utils
import Common.Keywords
import Common.PrettyPrint

data DefaultMorphism sign = MkMorphism sign sign deriving (Show, Eq)

instance PrettyPrint a => PrettyPrint (DefaultMorphism a) where
    printText0 ga (MkMorphism s t) =
        braces (printText0 ga s)
                    $$ nest 1 (text mapsTo)
                    <+> braces (printText0 ga t)

instance PrintLaTeX a => PrintLaTeX (DefaultMorphism a) where
    printLatex0 ga (MkMorphism s t) =
        sp_braces_latex (printLatex0 ga s)
                    $$ nest 1 (text mapsTo)
                    <\+> sp_braces_latex (printLatex0 ga t)

domOfDefaultMorphism, codOfDefaultMorphism :: DefaultMorphism sign -> sign
domOfDefaultMorphism (MkMorphism s _) = s
codOfDefaultMorphism (MkMorphism _ s) = s

ideOfDefaultMorphism :: sign -> DefaultMorphism sign
ideOfDefaultMorphism s = MkMorphism s s

compOfDefaultMorphism :: (Monad m, Eq sign) => DefaultMorphism sign
                      -> DefaultMorphism sign -> m (DefaultMorphism sign)
compOfDefaultMorphism (MkMorphism s1 s) (MkMorphism s2 s3) =
    if s == s2 then return $ MkMorphism s1 s3 else
    fail "intermediate signatures are different"

legalDefaultMorphism :: (sign -> Bool) -> DefaultMorphism sign -> Bool
legalDefaultMorphism legalSign (MkMorphism s t) =
    legalSign s && legalSign t

defaultInclusion :: (Monad m) => (sign -> sign -> Bool) -> sign -> sign
                 -> m (DefaultMorphism sign)
defaultInclusion isSubSig s1 s2 =
    if isSubSig s1 s2 then return $ MkMorphism s1 s2 else
    fail "non subsignatures for inclusion"
