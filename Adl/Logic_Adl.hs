{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  the Logic instance for ADL
Copyright   :  (c) Stef Joosten, Christian Maeder DFKI GmbH 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (import Logic.Logic)

-}

module Adl.Logic_Adl where

import Logic.Logic

import Adl.As
import Adl.Parse
import Adl.Print ()
import Adl.Sign
import Adl.StatAna
import Adl.ATC_Adl ()

import qualified Common.Lib.Rel as Rel
import Common.Id
import Common.GlobalAnnotations
import Common.Result
import Common.DefaultMorphism
import Common.ProofTree

import ATC.ProofTree ()

import qualified Data.Map as Map
import qualified Data.Set as Set

data Adl = Adl deriving Show

instance Language Adl where
    description _ = "A description language"

type Morphism = DefaultMorphism Sign

instance Sentences Adl
    Sen
    Sign
    Morphism
    Relation
    where
      sym_of Adl = singletonList . symOf
      symmap_of Adl _ = Map.empty
      sym_name Adl = stringToId . decnm
      map_sen Adl _ = return . id

instance Syntax Adl
    [PatElem]
    ()
    ()
    where
      parse_basic_spec Adl = Just pArchitecture
      parse_symb_items Adl = Nothing
      parse_symb_map_items Adl = Nothing

instance Logic Adl
    ()                -- Sublogics
    [PatElem]         -- basic_spec
    Sen               -- sentence
    ()                -- symb_items
    ()                -- symb_map_items
    Sign              -- sign
    Morphism          -- morphism
    Relation          -- symbol
    Relation          -- raw_symbol
    ProofTree         -- proof_tree
    where
       empty_proof_tree Adl = emptyProofTree
       provers Adl = []

instance GetRange PatElem
instance GetRange Relation

instance StaticAnalysis Adl
    [PatElem]
    Sen
    ()
    ()
    Sign
    Morphism
    Relation
    Relation
    where
      basic_analysis Adl = Just basicAna
      empty_signature Adl = emptySign
      is_subsig Adl = isSubSignOf
      signature_union Adl = signUnion
      symbol_to_raw Adl = id
      matches Adl = (==)
