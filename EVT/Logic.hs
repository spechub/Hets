{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- 

Instance of class Logic for EVTs
-}

module EVT.Logic where

import Common.DocUtils
import Common.Id

import Data.Monoid

import Logic.Logic

import EVT.AS
import EVT.Sign
import EVT.ParseEVT
import EVT.ATC_EVT ()
--import EVT.StaticAnalysis

import CASL.Logic_CASL

data EVT = EVT deriving (Show)

instance Language EVT where
    description _ =
        "Logic for the Institution EVT" 

-- | Instance of Category for EVT
instance Category
        EVTSign                    -- sign
        EVTMorphism             -- mor
        where
                dom = domain
                cod = codomain
               -- ide = idMor
               -- composeMorphisms = comp_mor

-- | Instance of Sentences for EVT
instance Sentences EVT EVENT EVTSign EVTMorphism EVTSymbol where			
    -- there is nothing to leave out
   simplify_sen EVT _ form = form
   print_named _ = printAnnoted pretty . fromLabelledSen
    --map_sen EVT = map_evt


instance Pretty EVENT where
instance Pretty MACHINE where
instance Pretty EVTMorphism where
instance Pretty EVTSign where
instance Pretty EVTSymbol where

instance Monoid EVENT where
     mempty = EVENT (stringToId "") [] []
     mappend (EVENT n1 g1 a1) (EVENT n2 g2 a2) = EVENT (mappend n1 n2) (mappend g1 g2) (mappend a1 a2) 

instance Monoid MACHINE where
     mempty = MACHINE []
     mappend (MACHINE m1) (MACHINE m2) = MACHINE (mappend m1 m2) 

instance Monoid EVTSign where
     mempty = emptyEVTSign
     mappend (EVTSign e1 g1) (EVTSign e2 g2) = EVTSign (mappend e1 e2) (mappend g1 g2) 

instance Monoid Id

-- | Syntax of EVT
instance Syntax EVT MACHINE EVTSymbol () () where--EVTMorphism () () where
     parse_basic_spec _ = Just $ evtBasicSpec
     parse_symb_items _ = Nothing
     parse_symb_map_items _ = Nothing

instance Logic EVT
    -- Sublogics (missing)
    ()
    -- basic_spec
    MACHINE
    EVENT
    -- sentence
    () -- symb_items
    () --symb map items
    EVTSign  -- Signature
        -- symb_map_items
   -- CspSymbMapItems
    -- signature
    -- morphism
    EVTMorphism 
    EVTSymbol  --  Symbol
    EVTRawSymbol
    -- proof_tree (missing)
    ()
    where
      stability (EVT)= Experimental
      data_logic (EVT) = Just (Logic CASL)
      empty_proof_tree _ = ()
     -- provers (GenCspCASL _) = cspProvers (undefined :: a)

{-- | Instance of Logic for EVT
instance Logic EVT
    ()                     -- Sublogics
    EVENT            -- basic_spec
    EVENT               -- sentence
    ()                     -- symb_items
    ()                     -- symb_map_items
    Sign                   -- sign
    EVTMorphism             -- morphism
    EVTSymbol               -- symbol
    () --  EVTRawSymbol            -- raw_symbol
    ()                     -- proof_tree
    where
      stability EVT = Experimental

- | Static Analysis for EVT-}
instance StaticAnalysis EVT
    MACHINE                    -- basic_spec
    EVENT--   Sentence
    ()                            -- symb_items
    ()                            -- symb_map_items
    EVTSign  -- sign                
    EVTMorphism                    -- morphism
    EVTSymbol                      -- symbol
    EVTRawSymbol                   -- raw_symbol
    where
      --basic_analysis EVT = Just basic_analysis
      empty_signature EVT = emptyEVTSign 
      --is_subsig EVT = isEVTSubsig
     -- subsig_inclusion EVT = evtInclusion
     -- signature_union EVT = uniteSig-}
