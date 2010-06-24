{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
module Framework.Logic_L where

import Logic.Logic

import LF.AS
import LF.Parse
import LF.Sign
import LF.Morphism
import LF.Framework

import Framework.Syntax

data L = L deriving Show

instance Language L where
   description L = "User-defined logic."

instance Syntax L BASIC_SPEC SYMB_ITEMS SYMB_MAP_ITEMS where
   parse_basic_spec L = Just basicSpec
   parse_symb_items L = Just symbItems
   parse_symb_map_items L = Just symbMapItems

instance Sentences L Sentence Sign Morphism Symbol
   
instance Logic L
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

instance StaticAnalysis L
   BASIC_SPEC
   Sentence
   SYMB_ITEMS
   SYMB_MAP_ITEMS
   Sign
   Morphism
   Symbol
   Symbol
   where
   empty_signature L = cod $ ltruth
   basic_analysis L = Just $ basicAnalysis ltruth
