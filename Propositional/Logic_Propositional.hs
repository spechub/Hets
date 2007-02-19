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
            , Morphism) where

import Logic.Logic
import Propositional.Sign as Sign
import Propositional.Morphism as Morphism
import Propositional.AS_BASIC_Propositional

data Propositional = Propositional deriving Show --lid

instance Language Propositional where
    description _ = 
        "Propositional Logic\n\
         \for more information please refer to\n\
         \http://en.wikipedia.org/wiki/Propositional_logic"

instance Category Propositional Sign Morphism where
    -- Identity morhpism
    ide Propositional = idMor
    -- Returns the domain of a morphism
    dom Propositional = source
    -- Returns the codomain of a morphism
    cod Propositional = target
    -- all sets are legal objects
    legal_obj Propositional s = isLegalSignature s
    -- tests if the morphism is ok
    legal_mor Propositional f = isLegalMorphism f
    -- composition of morphisms
    comp Propositional f g = composeMor f g
