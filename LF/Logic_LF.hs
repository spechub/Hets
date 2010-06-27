{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  Instances of classes defined in Logic.hs for the Edinburgh
               Logical Framework
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable
-}

module LF.Logic_LF where

import LF.AS
import LF.Parse
import LF.Sign
import LF.Morphism
import LF.ATC_LF ()
import LF.Analysis
import LF.Framework

import Logic.Logic

import qualified Data.Map as Map

data LF = LF deriving Show

instance Language LF where
   description LF = "Edinburgh Logical Framework"

instance Category Sign Morphism where
   ide = idMorph
   dom = source
   cod = target
   composeMorphisms = compMorph
   isInclusion = Map.null . symMap . canForm
   legal_mor = const True

instance Syntax LF BASIC_SPEC SYMB_ITEMS SYMB_MAP_ITEMS where
   parse_basic_spec LF = Just basicSpec
   parse_symb_items LF = Just symbItems
   parse_symb_map_items LF = Just symbMapItems

instance Sentences LF Sentence Sign Morphism Symbol

instance Logic LF
   ()
   BASIC_SPEC
   Sentence
   SYMB_ITEMS
   SYMB_MAP_ITEMS
   Sign
   Morphism
   Symbol
   Symbol
   ()

instance StaticAnalysis LF
   BASIC_SPEC
   Sentence
   SYMB_ITEMS
   SYMB_MAP_ITEMS
   Sign
   Morphism
   Symbol
   Symbol
   where
   empty_signature LF = emptySig
   basic_analysis LF = Just $ basicAnalysis

instance LogicFram LF
   ()
   BASIC_SPEC
   Sentence
   SYMB_ITEMS
   SYMB_MAP_ITEMS
   Sign
   Morphism
   Symbol
   Symbol
   ()
   where
   getBaseSig LF = baseSigLF
   writeLogic LF = writeLogicLF
   writeSyntax LF = writeSyntaxLF
