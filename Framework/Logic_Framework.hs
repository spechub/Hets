{- |
Module      :  $Header$
Description :  Instances of classes defined in Logic.hs for logical frameworks               
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable
-}

module Framework.Logic_Framework where

import Framework.AS
import Framework.Parse
import Framework.ATC_Framework ()
import Logic.Logic
import Common.Result

-- lid for logical frameworks
data Framework = Framework deriving Show

instance Language Framework where
   description _ = "Logical Framework"                   

-- instance of Category for Framework
instance Category () () where
  ide _ = ()
  dom _ = ()
  cod _ = ()
  legal_mor _ = True
  composeMorphisms _ _ = Result [] $ Just ()

-- syntax for DFOL
instance Syntax Framework BASIC_SPEC () () where
   parse_basic_spec Framework = Just basicSpecP

-- sentences for DFOL
instance Sentences Framework () () () ()

-- static analysis for Framework
instance StaticAnalysis Framework
   BASIC_SPEC
   ()
   ()
   ()
   ()
   ()
   ()
   ()
   where
   empty_signature Framework = () 

-- instance of logic for Framework
instance Logic Framework
   ()
   BASIC_SPEC
   ()
   ()
   ()
   ()
   ()
   ()
   ()
   ()
