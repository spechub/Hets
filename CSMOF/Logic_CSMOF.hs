{- |
Module      :  $Header$
Description :  Instance of class Logic for the CSMOF logic
Copyright   :  (c) Daniel Calegari Universidad de la Republica, Uruguay 2013
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  dcalegar@fing.edu.uy
Stability   :  provisional
Portability :  portable
-}

module CSMOF.Logic_CSMOF where

import CSMOF.As
import CSMOF.Sign
import CSMOF.StatAna

import Logic.Logic

import Common.DefaultMorphism
import Common.ProofTree

data CSMOF = CSMOF deriving Show

instance Language CSMOF where
    description _ = "CSMOF conformance relation"

type Morphism = DefaultMorphism Sign


-- CSMOF logic

instance Sentences CSMOF
    Sen
    Sign
    Morphism
    ()
--    where
--      map_sen CSMOF mor sen = return (mor sen)


instance Logic CSMOF
    ()                -- Sublogics
    Metamodel         -- basic_spec
    Sen               -- sentence
    ()                -- symb_items
    ()                -- symb_map_items
    Sign              -- sign
    Morphism	      -- morphism
    ()		      -- symbol
    ()		      -- raw_symbol
    ()		      -- proof_tree
    where
      stability CSMOF = Experimental
      empty_proof_tree _ = ()


instance StaticAnalysis CSMOF
    Metamodel		-- basic_spec
    Sen                 -- sentence
    ()                  -- symb_items
    ()                  -- symb_map_items
    Sign                -- sign
    Morphism         	-- morphism
    ()                  -- symbol
    ()                  -- raw_symbol
    where
      basic_analysis CSMOF = Just basicAna
      empty_signature CSMOF = emptySign
