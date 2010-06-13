{- |
Module      :  $Header$
Description :  Abstract syntax for logic definitions
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable
-}

module Framework.AS where

import Common.Id
import Common.Doc
import Common.DocUtils
import Common.Keywords

type NAME = Token
type SIG_NAME = Token
type MORPH_NAME = Token
type PATTERN_NAME = Token

data FRAM = LF | Isabelle | Maude deriving (Ord, Eq, Show)

data LogicDef = LogicDef
  { -- the name of the object logic
    newlogicName  :: NAME,     
    -- the framework used for defining the object logic
    meta          :: FRAM,
     -- name of the signature specifying the syntax of the object logic
    syntax        :: SIG_NAME,
    {- name of the morphism specifying the sentences and truth judgement of the
       object logic -}    
    truth         :: MORPH_NAME,
    -- name of the pattern specifying the signature category of the object logic
    signatures    :: PATTERN_NAME,
    -- name of the morphism specifying the model category of the object logic     
    models        :: MORPH_NAME,
    -- name of the morphism specifying the proof category of the object logic     
    proofs        :: MORPH_NAME
  } deriving (Ord, Eq, Show)

instance GetRange LogicDef

instance Pretty LogicDef where
    pretty = printLogicDef
instance Pretty FRAM where
    pretty = printFram

printLogicDef :: LogicDef -> Doc
printLogicDef (LogicDef l f sy t si m p) = 
  vcat [ text newlogicS <+> pretty l
       , text " " <+> text metaS <+> pretty f
       , text " " <+> text syntaxS <+> pretty sy
       , text " " <+> text truthS <+> pretty t
       , text " " <+> text signaturesS <+> pretty si
       , text " " <+> text modelsS <+> pretty m
       , text " " <+> text proofsS <+> pretty p
       ] 

printFram :: FRAM -> Doc
printFram LF = text "LF"
printFram Isabelle = text "Isabelle"
printFram Maude = text "Maude"
