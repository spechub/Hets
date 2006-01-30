{- |
Module      :  $Header$
Copyright   :  (c) Paolo Torrini and Till Mossakowski and Uni Bremen 2004-2005
License     :  All rights reserved.

Maintainer  :  paolot@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The embedding comorphism from Haskell to Isabelle-HOLCF.
-}

module Comorphisms.Haskell2IsabelleHOLCF where

import Comorphisms.Hs2HOLCF as Hs2HOLCF

import Logic.Logic as Logic
import Logic.Comorphism

-- Haskell
import Haskell.Logic_Haskell as LH
import Haskell.HatParser as HatParser hiding (HsType)
import Haskell.HatAna as HatAna

-- Isabelle
import Isabelle.IsaSign as IsaSign
import Isabelle.Logic_Isabelle

-- Programatica
import PNT 
import TiPropDecorate

------------------------------ Comorphism -----------------------------------------
-- The identity of the comorphism
data Haskell2IsabelleHOLCF = Haskell2IsabelleHOLCF deriving (Show)

instance Language Haskell2IsabelleHOLCF -- default definition is okay

instance Comorphism Haskell2IsabelleHOLCF -- multi-parameter class Com.
               Haskell ()
               HatParser.HsDecls (TiPropDecorate.TiDecl PNT) () ()
               HatAna.Sign HaskellMorphism
               () () ()
               Isabelle () () IsaSign.Sentence () ()
               IsaSign.Sign 
               IsabelleMorphism () () ()  where
    sourceLogic Haskell2IsabelleHOLCF = Haskell
    sourceSublogic Haskell2IsabelleHOLCF = ()
    targetLogic Haskell2IsabelleHOLCF = Isabelle
    targetSublogic Haskell2IsabelleHOLCF = ()
    map_sentence Haskell2IsabelleHOLCF _ _ = 
        fail "map_sentence Haskell2IsabelleHOLCF not supoorted"
    map_morphism Haskell2IsabelleHOLCF mor = do
       (sig1,_) <- map_sign Haskell2IsabelleHOLCF (Logic.dom Haskell mor)
       (sig2,_) <- map_sign Haskell2IsabelleHOLCF (cod Haskell mor)
       inclusion Isabelle sig1 sig2
    map_theory Haskell2IsabelleHOLCF (sign, sens) = do
        (sign',sens') <- Hs2HOLCF.transTheory IsCont False sign sens
        return (sign', sens')
    map_symbol Haskell2IsabelleHOLCF _ = 
        error "Haskell2IsabelleHOLCF.map_symbol"


