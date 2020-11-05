{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances, DeriveGeneric #-}
{- |
Module      :  ./Adl/Logic_Adl.hs
Description :  the Logic instance for ADL
Copyright   :  (c) Stef Joosten, Christian Maeder DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (import Logic.Logic)

see
Stef Joosten:
Deriving Functional Specifications from Business Requirements with Ampersand

and
https://lab.cs.ru.nl/BusinessRules/Requirements_engineering
-}

module Adl.Logic_Adl where

import Adl.As
import Adl.Parse
import Adl.Print ()
import Adl.Sign
import Adl.StatAna
import Adl.ATC_Adl ()

import ATC.ProofTree ()

import Common.DefaultMorphism
import Common.ProofTree
import Common.DocUtils

import Control.Monad
import qualified Data.HashMap.Lazy as Map
import Data.Monoid

import Logic.Logic
import GHC.Generics (Generic)
import Data.Hashable

data Adl = Adl deriving (Show, Generic)

instance Hashable Adl

instance Language Adl where
    description _ = "A description language for business rules"

type Morphism = DefaultMorphism Sign

instance Sentences Adl
    Sen
    Sign
    Morphism
    Symbol
    where
      sym_of Adl = singletonList . symOf
      symmap_of Adl _ = Map.empty
      sym_name Adl = symName
      map_sen Adl _ = return . id
      print_named Adl = printNSen
      symKind Adl = show . pretty . sym_kind

instance Monoid Context where
    mempty = Context Nothing []
    mappend (Context m1 l1) (Context m2 l2) = Context (mplus m1 m2) $ l1 ++ l2

instance Syntax Adl
    Context
    Symbol
    ()
    ()
    where
      parse_basic_spec Adl = Just $ const pArchitecture
      parse_symb_items Adl = Nothing
      parse_symb_map_items Adl = Nothing

instance Logic Adl
    ()                -- Sublogics
    Context           -- basic_spec
    Sen               -- sentence
    ()                -- symb_items
    ()                -- symb_map_items
    Sign              -- sign
    Morphism          -- morphism
    Symbol            -- symbol
    RawSymbol         -- raw_symbol
    ProofTree         -- proof_tree
    where
       empty_proof_tree Adl = emptyProofTree
       provers Adl = []
       stability Adl = Testing

instance StaticAnalysis Adl
    Context
    Sen
    ()
    ()
    Sign
    Morphism
    Symbol
    RawSymbol
    where
      basic_analysis Adl = Just basicAna
      empty_signature Adl = emptySign
      is_subsig Adl = isSubSignOf
      signature_union Adl = signUnion
      symbol_to_raw Adl = Symbol
      matches Adl = symMatch
