{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances, DeriveGeneric #-}
{- |
Module      :  ./Framework/Logic_Framework.hs
Description :  Instances of Logic and other classes for the logic Framework
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable

  Signatures of this logic are composed of a logical framework name
    (currently one of LF, Isabelle, or Maude) to be used as a meta-logic,
    and a tuple of signature and morphism names which determine
    the object logic. As such the logic Framework does not have any
    sentences and only identity signature morphisms.

  For reference see Integrating Logical Frameworks in Hets by M. Codescu et al
    (WADT10).
-}

module Framework.Logic_Framework where

import Framework.AS
import Framework.ATC_Framework ()

import Logic.Logic

import Data.Monoid

import Common.DefaultMorphism
import GHC.Generics (Generic)
import Data.Hashable

type Morphism = DefaultMorphism LogicDef

-- lid for logical frameworks
data Framework = Framework deriving (Show, Generic)

instance Hashable Framework

instance Language Framework where
   description _ = "A framework allowing to add logics dynamically."

instance Monoid LogicDef where
   mempty = error "Framework.Logic_Framework: Monoid LogicDef"
   mappend _ _ = mempty

-- syntax for Framework
instance Syntax Framework LogicDef () () ()

-- sentences for Framework
instance Sentences Framework () LogicDef Morphism ()

-- static analysis for Framework
instance StaticAnalysis Framework LogicDef () () ()
         LogicDef Morphism () () where
  empty_signature Framework = error
       "Logic Framework does not have an empty signature."

-- instance of logic for Framework
instance Logic Framework () LogicDef () () () LogicDef Morphism () () ()


{- ------------------------------------------------------------------------------
FrameworkCom -     logical framework for the analysis of comorphisms -}
type MorphismCom = DefaultMorphism ComorphismDef

data FrameworkCom = FrameworkCom deriving (Show, Generic)

instance Hashable FrameworkCom

instance Language FrameworkCom where
   description _ = "A framework allowing to add comorphisms between " ++
                   "logics dynamically."

instance Monoid ComorphismDef where
   mempty = error "Framework.Logic_Framework Monoid ComorphismDef"
   mappend _ _ = mempty

-- syntax for Framework
instance Syntax FrameworkCom ComorphismDef () () ()

-- sentences for Framework
instance Sentences FrameworkCom () ComorphismDef MorphismCom ()

-- static analysis for Framework
instance StaticAnalysis FrameworkCom ComorphismDef () () ()
         ComorphismDef MorphismCom () () where
  empty_signature FrameworkCom = error
       "Logic FrameworkCom does not have an empty signature."

-- instance of logic for Framework
instance Logic FrameworkCom () ComorphismDef () () () ComorphismDef
         MorphismCom () () ()
