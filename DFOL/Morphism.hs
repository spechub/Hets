{- |
Module      :  $Header$
Description :  Definition of signature morphisms for first-order logic with dependent types (DFOL)
-}

module DFOL.Morphism where

import DFOL.Sign
import Common.Result
import Common.Doc
import Common.DocUtils

-- morphisms for DFOL - so far just the identity morphisms
data Morphism = Morphism {object :: Sign} deriving (Show, Ord, Eq)

idMorph :: Sign -> Morphism
idMorph sig = Morphism {object = sig}

compMorph :: Morphism -> Morphism -> Result Morphism
compMorph m1 m2 = if object m1 == object m2
                     then return m1
                     else fail "Codomain of the first morphism must equal the domain of the second."

isValidMorph :: Morphism -> Bool
isValidMorph _ = True

-- pretty printing
instance Pretty Morphism where
   pretty = printMorph

printMorph :: Morphism -> Doc
printMorph m = text "Identity on" <+> (pretty $ object m)

