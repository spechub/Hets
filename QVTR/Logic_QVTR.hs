{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
{- |
Module      :  ./QVTR/Logic_QVTR.hs
Description :  Instance of class Logic for the QVTR logic
Copyright   :  (c) Daniel Calegari Universidad de la Republica, Uruguay 2013
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  dcalegar@fing.edu.uy
Stability   :  provisional
Portability :  portable
-}

module QVTR.Logic_QVTR where

import QVTR.As
import QVTR.Sign
import QVTR.Print ()
import QVTR.StatAna

import QVTR.ATC_QVTR ()

import Logic.Logic

import Common.DefaultMorphism

import Data.Monoid

data QVTR = QVTR deriving Show

instance Language QVTR where
  description _ = "OMG's QVT-Relations transformation, a language for the specification of model transformations"

type Morphism = DefaultMorphism Sign


-- QVTR logic

instance Monoid Transformation where
  mempty = error "Not implemented!"
  mappend _ _ = error "Not implemented!"

instance Sentences QVTR
  Sen
  Sign
  Morphism
  ()
  where
    map_sen QVTR _ = return


instance Syntax QVTR
  Transformation
  ()
  ()
  ()


instance Logic QVTR
  ()                -- Sublogics
  Transformation    -- basic_spec
  Sen               -- sentence
  ()                -- symb_items
  ()                -- symb_map_items
  Sign              -- sign
  Morphism          -- morphism
  ()                -- symbol
  ()                -- raw_symbol
  ()                -- proof_tree
  where
    stability QVTR = Experimental
    empty_proof_tree _ = ()


instance StaticAnalysis QVTR
  Transformation    -- basic_spec
  Sen               -- sentence
  ()                -- symb_items
  ()                -- symb_map_items
  Sign              -- sign
  Morphism          -- morphism
  ()                -- symbol
  ()                -- raw_symbol
  where
    basic_analysis QVTR = Just basicAna
    empty_signature QVTR = emptySign
    is_subsig QVTR _ _ = True
    subsig_inclusion QVTR = defaultInclusion
    induced_from_morphism _ _ sig = return $ MkMorphism sig sig
    signature_union QVTR sign1 _ = return sign1 -- TODO
