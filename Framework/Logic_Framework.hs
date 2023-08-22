{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
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

import Data.Monoid ()

import Common.DefaultMorphism

type Morphism = DefaultMorphism LogicDef

-- lid for logical frameworks
data Framework = Framework deriving Show

instance Language Framework where
   description _ = "A framework allowing to add logics dynamically."

instance Semigroup LogicDef where
   _ <> _ = mempty
instance Monoid LogicDef where
   mempty = error "Framework.Logic_Framework: Monoid LogicDef"

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

data FrameworkCom = FrameworkCom deriving Show

instance Language FrameworkCom where
   description _ = "A framework allowing to add comorphisms between " ++
                   "logics dynamically."

instance Semigroup ComorphismDef where
   _ <> _ = mempty
instance Monoid ComorphismDef where
   mempty = error "Framework.Logic_Framework Monoid ComorphismDef"

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
