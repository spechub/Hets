{-# LANGUAGE MultiParamTypeClasses #-}
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

import HolLight.Sign (Sign,emptySig,isSubSig)
import HolLight.Sentence (Sentence)
import HolLight.ATC_HolLight ()
import HolLight.Parse_AS_Basic


import Common.DefaultMorphism

type HolLightMorphism = DefaultMorphism Sign

data HolText = HolText String

-- | Lid for HolLight logic
data HolLight = HolLight deriving Show

instance Language HolLight where
    description _ = "Hol Light\n"
        ++ "for more information please refer to\n"
        ++ "http://www.cl.cam.ac.uk/~jrh13/hol-light/"

instance Syntax HolLight BasicSpec () () where
    parse_basic_spec HolLight = Nothing --Just basicSpec
    -- default implementation should be sufficient

instance Sentences HolLight () Sentence () () Sign HolLightMorphism () () where
    map_sen HolLight _ s = s
    --print_named HolLight = printNamedSen
    --other default implementations should be sufficient

-- | Instance of Logic for propositional logc
instance Logic HolLight
    ()                        -- sublogic
    HolText                   -- basic_spec
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
    HolText                  -- basic_spec
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

instance LogicFram HolLight () HolText Sentence () () Sign HolLightMorphism () () ()
