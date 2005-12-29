{- |
Module      :  $Header$
Copyright   :  (c) C. Maeder, and Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable (imports DynamicUtils, ATermLib, LaTeX)

supply a default morphism for a given signature
(due to functional deps the instance for Logic.Category cannot be supplied)
-}

module Common.DefaultMorphism where

import Common.Lib.Pretty
import Common.LaTeX_utils
import Common.LaTeX_funs
import Common.Keywords
import Common.PrettyPrint
import Common.ATerm.Lib
import Common.DynamicUtils
import Data.Dynamic

data DefaultMorphism sign = MkMorphism sign sign deriving (Show, Eq)

morTc :: TyCon
morTc = mkTyCon "Common.DefaultMorphism.DefaultMorphism"

instance Typeable a => Typeable (DefaultMorphism a) where
  typeOf s = mkTyConApp morTc [typeOf ((undefined:: DefaultMorphism a -> a) s)]

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

instance (ShATermConvertible a) => ShATermConvertible (DefaultMorphism a) where
    toShATerm att0 (MkMorphism s t) =
        case toShATerm att0 s of {  (att1, s') ->
        case toShATerm att1 t of {  (att2, t') ->
        addATerm (ShAAppl "MkMorphism" [ s', t'] []) att2 }}
    fromShATerm att =
        case getATerm att of
            ShAAppl "MkMorphism" [ s, t ] _ ->
                    case fromShATerm (getATermByIndex1 s att) of {  s' ->
                    case fromShATerm (getATermByIndex1 t att) of {  t' ->
                    (MkMorphism s' t') }}
            u -> fromShATermError "DefaultMorphism" u
    type_of _ = "DefaultMorphism"

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
