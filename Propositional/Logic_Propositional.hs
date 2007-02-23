{-# OPTIONS -fallow-undecidable-instances #-}
{- |
Module      :  $Header$
Description :  Instance of class Logic for propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@tzi.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

Instance of class Logic for the propositional logic
   Also the instances for Syntax and Category.
-}

{-
  Ref.

  http://en.wikipedia.org/wiki/Propositional_logic

  Till Mossakowski, Joseph Goguen, Razvan Diaconescu, Andrzej Tarlecki.
  What is a Logic?.
  In Jean-Yves Beziau (Ed.), Logica Universalis, pp. 113-@133. Birkhäuser.
  2005.
-}

module Propositional.Logic_Propositional 
    (module Propositional.Logic_Propositional
            , Sign
            , Morphism
    ) where
    
import Logic.Logic
import Propositional.Sign as Sign
import Propositional.Morphism as Morphism
import qualified Propositional.AS_BASIC_Propositional as AS_BASIC
import qualified Propositional.ATC_Propositional()
import qualified Propositional.Symbol as Symbol

-- | Lid for propositional logic
data Propositional = Propositional deriving Show --lid

instance Language Propositional where
    description _ = 
        "Propositional Logic\n\
         \for more information please refer to\n\
         \http://en.wikipedia.org/wiki/Propositional_logic"

-- | Instance of Category for propositional logic
instance Category Propositional Sign.Sign Morphism.Morphism where
    -- Identity morhpism
    ide Propositional = Morphism.idMor
    -- Returns the domain of a morphism
    dom Propositional = Morphism.source
    -- Returns the codomain of a morphism
    cod Propositional = Morphism.target
    -- all sets are legal objects
    legal_obj Propositional s = Sign.isLegalSignature s
    -- tests if the morphism is ok
    legal_mor Propositional f = Morphism.isLegalMorphism f
    -- composition of morphisms
    comp Propositional f g = Morphism.composeMor f g

-- | Instance of Sentences for propositional logic
instance Sentences Propositional AS_BASIC.FORMULA () 
    Sign.Sign Morphism.Morphism Symbol.Symbol where
    -- returns the set of symbols
    sym_of Propositional = Symbol.symOf
    -- returns the symbol map
    symmap_of Propositional = Symbol.getSymbolMap
    -- returns the name of a symbol
    sym_name Propositional = Symbol.getSymbolName
    -- default entry
    empty_proof_tree Propositional = error "Not yet implemented"

-- | Syntax of Propositional logic
instance Syntax Propositional AS_BASIC.BASIC_SPEC 
    AS_BASIC.SYMB_ITEMS AS_BASIC.SYMB_MAP_ITEMS where
         parse_basic_spec _ = Nothing
         parse_symb_items _ = Nothing
         parse_symb_map_items _ = Nothing
