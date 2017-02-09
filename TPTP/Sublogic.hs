{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./TPTP/Sublogic.hs
Description :  Data structures representing TPTP sublogics.
Copyright   :  (c) Eugen Kuksa University of Magdeburg 2017
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Eugen Kuksa <kuksa@iks.cs.ovgu.de>
Stability   :  provisional

Data structures representing TPTP sublogics.
-}

module TPTP.Sublogic where

import TPTP.AS
import TPTP.Sign

import Common.AS_Annotation (item)
import Common.DefaultMorphism

import Data.Data
import qualified Data.Map as Map
import qualified Data.Set as Set

              -- | EPR -- Effectively Propositional CNF
data Sublogic = CNF -- Clausal Normal Form
              | FOF -- First Order Form
              -- | TCF
              | TFF -- Typed First Order Form
              -- | TFX
              | THF -- Typed Higher Order Form
              -- | TPI
                deriving (Show, Ord, Eq, Data, Typeable)

{- ----------------------------------------------------------------------------
 - Special Sublogics
---------------------------------------------------------------------------- -}
top :: Sublogic
top = THF

bottom :: Sublogic
bottom = CNF


{- ----------------------------------------------------------------------------
 - Utility functions
---------------------------------------------------------------------------- -}
sublogicName :: Sublogic -> String
sublogicName = show

leastUpperBound :: Sublogic -> Sublogic -> Sublogic
leastUpperBound = max


{- ----------------------------------------------------------------------------
 - Determine sublogics
---------------------------------------------------------------------------- -}
sublogicOfUnit :: Sublogic -> () -> Sublogic
sublogicOfUnit sublogic () = bottom

sublogicOfBaiscSpec :: Sublogic -> BASIC_SPEC -> Sublogic
sublogicOfBaiscSpec sublogic basicSpec = case basicSpec of
  Basic_spec annotedTPTPs -> foldr leastUpperBound sublogic $
    map (sublogicOfTPTP sublogic . item) annotedTPTPs
  where
    sublogicOfTPTP :: Sublogic -> TPTP -> Sublogic
    sublogicOfTPTP sublogic tptp = case tptp of
      TPTP tptp_inputs -> foldr leastUpperBound sublogic $
        map (sublogicOfTPTPInput sublogic) tptp_inputs

    sublogicOfTPTPInput :: Sublogic -> TPTP_input -> Sublogic
    sublogicOfTPTPInput sublogic tptp_input = case tptp_input of
      Annotated_formula annotated_formula ->
        sublogicOfSentence sublogic annotated_formula
      _ -> sublogic

sublogicOfSentence :: Sublogic -> Sentence -> Sublogic
sublogicOfSentence sublogic sentence = case sentence of
  AF_THF_Annotated _ -> THF
  AF_TFX_Annotated _ -> THF
  AF_TFF_Annotated _ -> TFF
  AF_TCF_Annotated _ -> TFF
  AF_FOF_Annotated _ -> FOF
  AF_CNF_Annotated _ -> CNF
  AF_TPI_Annotated _ -> THF

sublogicOfSymbol :: Sublogic -> Symbol -> Sublogic
sublogicOfSymbol sublogic symbol = bottom

sublogicOfSign :: Sublogic -> Sign -> Sublogic
sublogicOfSign sublogic sign = case () of
  _ | not $ Map.null $ thfTypeConstantMap sign -> THF
  _ | not $ Map.null $ thfTypeFunctorMap sign -> THF
  _ | not $ Map.null $ thfPredicateMap sign -> THF
  _ | not $ Map.null $ thfSubtypeMap sign -> THF
  _ | not $ Map.null $ tffTypeConstantMap sign -> TFF
  _ | not $ Map.null $ tffTypeFunctorMap sign -> TFF
  _ | not $ Map.null $ tffPredicateMap sign -> TFF
  _ | not $ Map.null $ tffSubtypeMap sign -> TFF
  _ | not $ Set.null $ numberSet sign -> TFF
  _ | not $ Map.null $ fofPredicateMap sign -> FOF
  _ | not $ Map.null $ fofFunctorMap sign -> FOF
  _ -> bottom

sublogicOfMorphism :: Sublogic -> Morphism -> Sublogic
sublogicOfMorphism sublogic morphism =
  leastUpperBound
    (sublogicOfSign sublogic $ domOfDefaultMorphism morphism)
    (sublogicOfSign sublogic $ codOfDefaultMorphism morphism)


{- ----------------------------------------------------------------------------
 - Determine projections
---------------------------------------------------------------------------- -}
-- TODO: complete the projections

projectSublogicBasicSpec :: Sublogic -> BASIC_SPEC -> BASIC_SPEC
projectSublogicBasicSpec sublogic basicSpec = basicSpec

projectSublogicSign :: Sublogic -> Sign -> Sign
projectSublogicSign sublogic sign = sign

projectSublogicSentence :: Sublogic -> Sentence -> Sentence
projectSublogicSentence sublogic sentence = sentence

projectSublogicMorphism :: Sublogic -> Morphism -> Morphism
projectSublogicMorphism sublogic morphism = morphism


projectSublogicMUnit :: Sublogic -> () -> Maybe ()
projectSublogicMUnit sublogic = Just

projectSublogicMSymbol :: Sublogic -> Symbol -> Maybe Symbol
projectSublogicMSymbol sublogic symbol = Just symbol
