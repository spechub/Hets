module DFOL.Logic_DFOL where

import DFOL.AS_DFOL
import DFOL.Sign
import DFOL.Morphism
import DFOL.Parse_AS_DFOL
import DFOL.ATC_DFOL ()
import DFOL.Analysis_DFOL
import DFOL.Symbol
import Logic.Logic
import Common.Result
import qualified Data.Map as Map 

-- lid for first-order logic with dependent types
data DFOL = DFOL deriving Show

instance Language DFOL where
   description _ = "First-Order Logic with Dependent Types\n" 
                   ++ "developed by F. Rabe"

-- instance of Category for DFOL
instance Category Sign Morphism where
   ide = idMorph
   dom = source
   cod = target
   isInclusion = Map.null . symMap
   composeMorphisms = compMorph
   legal_mor = isValidMorph

-- syntax for DFOL
instance Syntax DFOL BASIC_SPEC SYMB_ITEMS SYMB_MAP_ITEMS where
   parse_basic_spec DFOL = Just basicSpec
   parse_symb_items DFOL = Just symbItems
   parse_symb_map_items DFOL = Just symbMapItems

-- sentences for DFOL
instance Sentences DFOL FORMULA Sign Morphism Symbol where
   map_sen DFOL m = wrapInResult . (applyMorphism m)

-- static analysis for DFOL
instance StaticAnalysis DFOL
   BASIC_SPEC
   FORMULA
   SYMB_ITEMS
   SYMB_MAP_ITEMS
   Sign
   Morphism
   Symbol
   Symbol
   where
   basic_analysis DFOL = Just basicAnalysis
   stat_symb_map_items DFOL = symbMapAnalysis
   stat_symb_items DFOL = symbAnalysis
   empty_signature DFOL = emptySig

-- instance of logic for DFOL
instance Logic DFOL
   ()
   BASIC_SPEC
   FORMULA
   SYMB_ITEMS
   SYMB_MAP_ITEMS
   Sign
   Morphism
   Symbol
   Symbol
   ()

-- creates a Result
wrapInResult :: a -> Result a
wrapInResult x = Result [] $ Just x
