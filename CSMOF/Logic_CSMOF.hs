{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, DeriveGeneric #-}
{- |
Module      :  ./CSMOF/Logic_CSMOF.hs
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
import CSMOF.Print ()
import CSMOF.StatAna
import CSMOF.ATC_CSMOF ()

import Logic.Logic

import Common.DefaultMorphism

import Data.Monoid
import GHC.Generics (Generic)
import Data.Hashable

data CSMOF = CSMOF deriving (Show, Generic)

instance Hashable CSMOF

instance Language CSMOF where
  description _ = "OMG's meta-object facility, a language for the specification of metamodels"

type Morphism = DefaultMorphism Sign


-- CSMOF logic

instance Monoid Metamodel where
  mempty = error "Not implemented!"
  mappend _ _ = error "Not implemented!"

instance Sentences CSMOF
  Sen
  Sign
  Morphism
  ()
  where
    map_sen CSMOF _ = return


instance Syntax CSMOF
  Metamodel
  ()
  ()
  ()


instance Logic CSMOF
  ()                -- Sublogics
  Metamodel         -- basic_spec
  Sen               -- sentence
  ()                -- symb_items
  ()                -- symb_map_items
  Sign              -- sign
  Morphism          -- morphism
  ()                -- symbol
  ()                -- raw_symbol
  ()                -- proof_tree
  where
    stability CSMOF = Experimental
    empty_proof_tree _ = ()


instance StaticAnalysis CSMOF
  Metamodel         -- basic_spec
  Sen               -- sentence
  ()                -- symb_items
  ()                -- symb_map_items
  Sign              -- sign
  Morphism          -- morphism
  ()                -- symbol
  ()                -- raw_symbol
  where
    basic_analysis CSMOF = Just basicAna
    empty_signature CSMOF = emptySign
    is_subsig CSMOF _ _ = True
    subsig_inclusion CSMOF = defaultInclusion
    induced_from_morphism _ _ sig = return $ MkMorphism sig sig
    signature_union CSMOF sign1 _ = return sign1 -- TODO
