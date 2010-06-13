{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  Instances of Logic and other classes for the logic Framework               
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

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

import Common.DefaultMorphism

type Morphism = DefaultMorphism LogicDef

-- lid for logical frameworks
data Framework = Framework deriving Show

instance Language Framework where
   description _ = "A framework allowing to add logics dynamically."

-- syntax for Framework
instance Syntax Framework LogicDef () () 

-- sentences for Framework
instance Sentences Framework () LogicDef Morphism ()
   
-- static analysis for Framework
instance StaticAnalysis Framework LogicDef () () ()
         LogicDef Morphism () () where 
  empty_signature Framework = error 
       "Logic Framework does not have an empty signature."
 
-- instance of logic for Framework
instance Logic Framework () LogicDef () () () LogicDef Morphism () () ()

