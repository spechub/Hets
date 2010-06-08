{-# LANGUAGE MultiParamTypeClasses #-}
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
import Framework.Parse
import Framework.Analysis
import Logic.Logic
import Common.Result

-- lid for logical frameworks
data Framework = Framework deriving Show

instance Language Framework where
   description _ = "A framework allowing to add logics dynamically."

-- signature category for Framework
instance Category Sign Morphism where
  ide sig = Morphism sig 
  dom = object
  cod = object
  legal_mor = const True
  isInclusion = const True
  composeMorphisms m _ = Result [] $ Just m

-- syntax for Framework
instance Syntax Framework Sign () () where
   parse_basic_spec Framework = Just basicSpecP
   parse_symb_items Framework = error noStruct
   parse_symb_map_items Framework = error noStruct

-- sentences for Framework
instance Sentences Framework () Sign Morphism () where
   sym_of Framework = error noStruct   
   
-- static analysis for Framework
instance StaticAnalysis Framework Sign () () () Sign Morphism () () where
  basic_analysis Framework = Just basicAnalysis
  empty_signature Framework = error noEmptySig
 
-- instance of logic for Framework
instance Logic Framework () Sign () () () Sign Morphism () () ()

noEmptySig, noStruct :: String
noEmptySig = "Logic Framework does not have an empty signature."
noStruct = "No views or structuring in logic Framework allowed."
   
