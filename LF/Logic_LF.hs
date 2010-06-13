{-# LANGUAGE MultiParamTypeClasses #-}
{- |
Module      :  $Header$
Description :  Instances of classes defined in Logic.hs for the Edinburgh
               Logical Framework
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable
-}

module LF.Logic_LF where

import LF.Sign
import LF.Morphism
import LF.ATC_LF ()
import Logic.Logic
import qualified Data.Map as Map

-- lid for LF
data LF = LF deriving Show

instance Language LF where
   description _ = "Edinburgh Logical Framework"

-- instance of Category for LF
instance Category Sign Morphism where
   ide = idMorph
   dom = source
   cod = target
   composeMorphisms = compMorph
   isInclusion = Map.null . symMap . canForm
   legal_mor = const True

-- syntax for LF
instance Syntax LF () () ()

-- sentences for LF
instance Sentences LF () Sign Morphism ()

-- instance of logic for LF
instance Logic LF () () () () () Sign Morphism () () ()

-- static analysis for LF
instance StaticAnalysis LF () () () () Sign Morphism () () where
   empty_signature LF = emptySig

