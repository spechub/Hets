{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./Framework/AS.hs
Description :  Abstract syntax for logic definitions
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable
-}

module Framework.AS where

import Common.Id
import Common.IRI (IRI)
import Common.Doc
import Common.DocUtils
import Common.Keywords

import Data.Data

type NAME = IRI
type SIG_NAME = IRI
type MORPH_NAME = IRI
type PATTERN_NAME = Token

data FRAM = LF | Isabelle | Maude deriving (Show, Eq, Ord, Typeable, Data)

data LogicDef = LogicDef
  { -- the name of the object logic
    newlogicName :: NAME,
    -- the framework used for defining the object logic
    meta :: FRAM,
    {- name of the morphism specifying the sentences and truth judgement of the
       object logic -}
    syntax :: MORPH_NAME,
    -- name of the morphism specifying the model category of the object logic
    models :: MORPH_NAME,
    -- the foundation used to construct the model theory of the object logic
    foundation :: SIG_NAME,
    -- name of the morphism specifying the proof category of the object logic
    proofs :: MORPH_NAME,
    -- name of the pattern specifying the signature category of the object logic
    patterns :: PATTERN_NAME
  } deriving (Show, Eq, Ord, Typeable, Data)

data ComorphismDef = ComorphismDef
  { -- the name of the comorphism
    newcomorphismName :: NAME,
    -- the framework used for defining the comorphism
    metaC :: FRAM,
    -- name of the source logic
    source :: SIG_NAME,
    -- name of the target logic
    target :: SIG_NAME,
    {- name of the morphism between the syntax of the source logic and
       the syntax of the target logic -}
    syntaxC :: MORPH_NAME,
    {- name of the morphism between the model category of the source logic and
       the model category of the target logic -}
    modelC :: MORPH_NAME,
    {- name of the morphism between the proof category of the source logic and
       the proof category of the target logic -}
    proofC :: MORPH_NAME
  } deriving (Show, Eq, Ord, Typeable, Data)

instance GetRange LogicDef
instance GetRange ComorphismDef

instance Pretty LogicDef where
    pretty = printLogicDef
instance Pretty ComorphismDef where
    pretty = printComorphismDef
instance Pretty FRAM where
    pretty = printFram

printLogicDef :: LogicDef -> Doc
printLogicDef (LogicDef l ml s m f p pa) =
  vcat [ text newlogicS <+> pretty l
       , text " " <+> text metaS <+> pretty ml
       , text " " <+> text syntaxS <+> pretty s
       , text " " <+> text modelsS <+> pretty m
       , text " " <+> text foundationS <+> pretty f
       , text " " <+> text proofsS <+> pretty p
       , text " " <+> text patternsS <+> pretty pa
       ]

printComorphismDef :: ComorphismDef -> Doc
printComorphismDef (ComorphismDef c ml sl tl s m p) =
  vcat [ text newcomorphismS <+> pretty c
       , text " " <+> text metaS <+> pretty ml
       , text " " <+> text sourceS <+> pretty sl
       , text " " <+> text targetS <+> pretty tl
       , text " " <+> text syntaxS <+> pretty s
       , text " " <+> text modelsS <+> pretty m
       , text " " <+> text proofsS <+> pretty p
       ]

printFram :: FRAM -> Doc
printFram LF = text "LF"
printFram Isabelle = text "Isabelle"
printFram Maude = text "Maude"
