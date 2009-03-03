{- |
Module      :  $Header$
Description :  supply a default morphism for a given signature type
Copyright   :  (c) C. Maeder, and Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Supply a default morphism for a given signature type
-}

-- due to functional deps the instance for Logic.Category cannot be supplied

module Common.DefaultMorphism
  ( DefaultMorphism(..) -- constructor is only exported for ATC
  , ideOfDefaultMorphism
  , compOfDefaultMorphism
  , legalDefaultMorphism
  , mkDefaultMorphism
  , defaultInclusion
  ) where

import Common.Keywords
import Common.Doc
import Common.DocUtils

data DefaultMorphism sign = MkMorphism
  { domOfDefaultMorphism :: sign
  , codOfDefaultMorphism :: sign
  , isInclusionDefaultMorphism :: Bool
  } deriving (Show, Eq, Ord)

instance Pretty a => Pretty (DefaultMorphism a) where
    pretty = printDefaultMorphism pretty

printDefaultMorphism :: (a -> Doc) -> DefaultMorphism a -> Doc
printDefaultMorphism fA (MkMorphism s t b) =
    (if b then text "inclusion" else empty) $+$
    specBraces (fA s) $+$ text mapsTo <+> specBraces (fA t)

ideOfDefaultMorphism :: sign -> DefaultMorphism sign
ideOfDefaultMorphism s = MkMorphism s s True

compOfDefaultMorphism :: Monad m => DefaultMorphism sign
                      -> DefaultMorphism sign -> m (DefaultMorphism sign)
compOfDefaultMorphism (MkMorphism s1 _ b1) (MkMorphism _ s3 b2) =
    return $ MkMorphism s1 s3 $ min b1 b2

legalDefaultMorphism :: (sign -> Bool) -> DefaultMorphism sign -> Bool
legalDefaultMorphism legalSign (MkMorphism s t _) =
    legalSign s && legalSign t

mkDefaultMorphism :: sign -> sign -> DefaultMorphism sign
mkDefaultMorphism s1 s2 = MkMorphism s1 s2 False

defaultInclusion :: Monad m => sign -> sign -> m (DefaultMorphism sign)
defaultInclusion s1 s2 = return $ MkMorphism s1 s2 True

