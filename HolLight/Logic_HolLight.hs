{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  Instance of class Logic for HolLight

Copyright   :  (c) Jonathan von Schroeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  jonathan.von_schroeder@dfki.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

Instance of class Logic for HolLight logic
   Also the instances for Syntax and Category.

  Ref.

  <http://www.cl.cam.ac.uk/~jrh13/hol-light/>

-}

module HolLight.Logic_HolLight where

import Logic.Logic

import HolLight.Sign
import HolLight.Sublogic
import HolLight.Sentence (Sentence)
import HolLight.ATC_HolLight ()

import Common.DefaultMorphism
import Common.Id

type HolLightMorphism = DefaultMorphism Sign

-- | Lid for HolLight logic
data HolLight = HolLight deriving Show


instance Language HolLight where
    description _ = "Hol Light\n"
        ++ "for more information please refer to\n"
        ++ "http://www.cl.cam.ac.uk/~jrh13/hol-light/"

instance GetRange Sentence

instance Syntax HolLight () () () where
    parse_basic_spec HolLight = Nothing --Just basicSpec
    -- default implementation should be sufficient

instance Sentences HolLight Sentence Sign HolLightMorphism () where
    map_sen HolLight _ s = return s
    --other default implementations should be sufficient

-- | Sublogics
instance SemiLatticeWithTop HolLightSL where
    join _ _ = Top
    top = Top

instance MinSublogic HolLightSL () where
     minSublogic _ = Top

instance MinSublogic HolLightSL Sign where
    minSublogic _ = Top

instance SublogicName HolLightSL where
    sublogicName = show

instance MinSublogic HolLightSL HolLightMorphism where
    minSublogic _ = Top

instance MinSublogic HolLightSL Sentence where
    minSublogic _ = Top

instance ProjectSublogic HolLightSL () where
    projectSublogic _ = id

instance ProjectSublogic HolLightSL Sign where
    projectSublogic _ = id

instance ProjectSublogic HolLightSL HolLightMorphism where
    projectSublogic _ = id

instance ProjectSublogicM HolLightSL () where
    projectSublogicM _ = Just

-- | Instance of Logic for propositional logc
instance Logic HolLight
    HolLightSL                -- sublogic
    ()                        -- basic_spec
    Sentence                  -- sentence
    ()                        -- symb_items
    ()                        -- symb_map_items
    Sign                      -- sign
    HolLightMorphism          -- morphism
    ()                        -- symbol
    ()                        -- raw_symbol
    ()                        -- proof_tree
    where
      stability HolLight = Experimental
      empty_proof_tree _ = ()

-- | Static Analysis for propositional logic
instance StaticAnalysis HolLight
    ()                      -- basic_spec
    Sentence                 -- sentence
    ()                       -- symb_items
    ()                       -- symb_map_items
    Sign                     -- sign
    HolLightMorphism         -- morphism
    ()                       -- symbol
    ()                       -- raw_symbol
        where
           --basic_analysis HolLight = Just basicHolAnalysis
           empty_signature HolLight = emptySig
           is_subsig HolLight = isSubSig
           subsig_inclusion HolLight = defaultInclusion
