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
import CSMOF.StaticAna

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
    ()
    ()


instance Logic CSMOF
    ()                -- Sublogics
    Metamodel         -- basic_spec
    Sen               -- sentence
    ()                -- symb_items
    ()                -- symb_map_items
    Sign              -- sign
    ()		          -- morphism
    ()		            -- symbol
    ()		         -- raw_symbol
    ()		         -- proof_tree

instance StaticAnalysis Adl
    Metamodel
    Sen
    ()
    ()
    Sign
    ()
    ()
    ()
    where
      basic_analysis CSMOF = Just basicAna
      empty_signature CSMOF = emptySign

