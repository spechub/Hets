{- |
Module      :  $Header$
Copyright   :  (c) Paolo Torrini and Till Mossakowski and Uni Bremen 2004-2005
License     :  All rights reserved.

Maintainer  :  paolot@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The embedding comorphisms from Haskell to Isabelle
-}

module Comorphisms.Haskell2IsabelleHOLCF where

import Comorphisms.Hs2HOLCF as Hs2HOLCF

import Logic.Logic as Logic
import Logic.Comorphism

-- Haskell
import Haskell.Logic_Haskell
import Haskell.HatParser as HatParser
import Haskell.HatAna as HatAna

-- Isabelle
import Isabelle.IsaSign as IsaSign
import Isabelle.Logic_Isabelle

-- Programatica
import PNT
import TiPropDecorate

-- * Comorphisms

-- The identity of the comorphism
data Haskell2IsabelleHOLCF = Haskell2IsabelleHOLCF deriving (Show)

instance Language Haskell2IsabelleHOLCF

instance Comorphism Haskell2IsabelleHOLCF
               Haskell ()
               HsDecls (TiDecl PNT) () ()
               HatAna.Sign HaskellMorphism
               () () ()
               Isabelle () () IsaSign.Sentence () ()
               IsaSign.Sign
               IsabelleMorphism () () ()  where
    sourceLogic _ = Haskell
    sourceSublogic _ = ()
    targetLogic _ = Isabelle
    mapSublogic _ _ = ()
    map_sentence = failMapSentence
    map_morphism = mapDefaultMorphism
    map_theory _ (sign, sens) =
        Hs2HOLCF.transTheory IsCont False sign sens
    map_symbol = errMapSymbol

data Haskell2IsabelleHOL = Haskell2IsabelleHOL deriving (Show)

instance Language Haskell2IsabelleHOL

instance Comorphism Haskell2IsabelleHOL
               Haskell ()
               HsDecls (TiDecl PNT) () ()
               HatAna.Sign HaskellMorphism
               () () ()
               Isabelle () () IsaSign.Sentence () ()
               IsaSign.Sign
               IsabelleMorphism () () ()  where
    sourceLogic _ = Haskell
    sourceSublogic _ = ()
    targetLogic _ = Isabelle
    mapSublogic _ _ = ()
    map_sentence = failMapSentence
    map_morphism = mapDefaultMorphism
    map_theory _ (sign, sens) =
        Hs2HOLCF.transTheory NotCont False sign sens
    map_symbol = errMapSymbol

data Haskell2MorHOLCF = Haskell2MorHOLCF deriving (Show)

instance Language Haskell2MorHOLCF

instance Comorphism Haskell2MorHOLCF
               Haskell ()
               HsDecls (TiDecl PNT) () ()
               HatAna.Sign HaskellMorphism
               () () ()
               Isabelle () () IsaSign.Sentence () ()
               IsaSign.Sign
               IsabelleMorphism () () ()  where
    sourceLogic _ = Haskell
    sourceSublogic _ = ()
    targetLogic _ = Isabelle
    mapSublogic _ _ = ()
    map_sentence = failMapSentence
    map_morphism = mapDefaultMorphism
    map_theory _ (sign, sens) =
        Hs2HOLCF.transTheory IsCont True sign sens
    map_symbol = errMapSymbol

data Haskell2MorHOL = Haskell2MorHOL deriving (Show)

instance Language Haskell2MorHOL

instance Comorphism Haskell2MorHOL
               Haskell ()
               HsDecls (TiDecl PNT) () ()
               HatAna.Sign HaskellMorphism
               () () ()
               Isabelle () () IsaSign.Sentence () ()
               IsaSign.Sign
               IsabelleMorphism () () ()  where
    sourceLogic _ = Haskell
    sourceSublogic _ = ()
    targetLogic _ = Isabelle
    mapSublogic _ _ = ()
    map_sentence = failMapSentence
    map_morphism = mapDefaultMorphism
    map_theory _ (sign, sens) =
        Hs2HOLCF.transTheory NotCont True sign sens
    map_symbol = errMapSymbol
