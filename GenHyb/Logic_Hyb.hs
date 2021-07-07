{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./GenHyb/Logic_Hyb.hs
Description :  Instances of Logic and other classes for the logic Framework
Copyright   :  (c) M. Codescu, IMAR, 2018
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  mscodescu@gmail.com
Stability   :  experimental
Portability :  portable

-}

module GenHyb.Logic_Hyb where

import Framework.AS
import ATC.HDef ()

import Logic.Logic
-- import Logic.SemConstr
import Logic.HDef

import Data.Monoid

import Common.DefaultMorphism

type Morphism = DefaultMorphism HLogicDef

-- lid for the dummy logic
data Hyb = Hyb deriving Show

instance Language Hyb where
   description _ = "Dummy logic for dynamic generation of hybridized logics."

instance Monoid HLogicDef where
   mempty = error "GenHyb.Logic_Hyb: Monoid HLogicDef"
   mappend _ _ = mempty

-- syntax
instance Syntax Hyb HLogicDef () () ()

-- sentences
instance Sentences Hyb () HLogicDef Morphism ()

-- static analysis
instance StaticAnalysis Hyb HLogicDef () () ()
         HLogicDef Morphism () () where
  empty_signature Hyb = error
       "Logic Hyb does not have an empty signature."

-- instance of logic for Hyb
instance Logic Hyb () HLogicDef () () () HLogicDef Morphism () () ()
