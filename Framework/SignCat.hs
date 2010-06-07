{- |
Module      :  $Header$
Description :  Signatures for the logic Framework
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable
-}

module Framework.SignCat where

import Common.Id
import Common.Doc
import Common.DocUtils

type NAME = Token
type SIG_NAME = Token
type MORPH_NAME = Token
type PATTERN_NAME = Token
data FRAM = LF | Isabelle | Maude deriving (Ord, Eq, Show)

data Sign = Sign
  { -- name of the object logic
    logicName  :: NAME,
    -- the framework used for defining the object logic
    meta       :: FRAM,
     -- name of the signature specifying the syntax of the object logic
    syntax     :: SIG_NAME,
    {- name of the morphism specifying the sentences and truth judgement of the
       object logic -}    
    truth      :: MORPH_NAME,
    -- name of the pattern specifying the signature category of the object logic
    signatures :: PATTERN_NAME,
    -- name of the morphism specifying the model category of the object logic     
    models     :: MORPH_NAME,
    -- name of the morphism specifying the proof category of the object logic     
    proofs     :: MORPH_NAME
  } deriving (Ord, Eq, Show)

data Morphism = Morphism { object :: Sign } deriving (Ord, Eq, Show)

instance GetRange Sign

instance Pretty Morphism where
  pretty _ = text ""
instance Pretty Sign where
    pretty = printSign
instance Pretty FRAM where
    pretty = printFram

printSign :: Sign -> Doc
printSign (Sign l f sy t si m p) = 
  vcat [ text "logic" <+> pretty l <+> text "=" 
       , text " " <+> text "meta" <+> pretty f
       , text " " <+> text "syntax" <+> pretty sy
       , text " " <+> text "truth" <+> pretty t
       , text " " <+> text "signatures" <+> pretty si
       , text " " <+> text "models" <+> pretty m
       , text " " <+> text "proofs" <+> pretty p
       ] 

printFram :: FRAM -> Doc
printFram LF = text "LF"
printFram Isabelle = text "Isabelle"
printFram Maude = text "Maude"
