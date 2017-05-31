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
sublogicOfUnit minimumSublogic () = minimumSublogic

sublogicOfBaiscSpec :: Sublogic -> BASIC_SPEC -> Sublogic
sublogicOfBaiscSpec minimumSublogic basicSpec = case basicSpec of
  Basic_spec annotedTPTPs -> foldr leastUpperBound minimumSublogic $
    map (sublogicOfTPTP . item) annotedTPTPs
  where
    sublogicOfTPTP :: TPTP -> Sublogic
    sublogicOfTPTP tptp = case tptp of
      TPTP tptp_inputs -> foldr leastUpperBound minimumSublogic $
        map sublogicOfTPTPInput tptp_inputs

    sublogicOfTPTPInput :: TPTP_input -> Sublogic
    sublogicOfTPTPInput tptp_input = case tptp_input of
      Annotated_formula annotated_formula ->
        sublogicOfSentence minimumSublogic annotated_formula
      _ -> minimumSublogic

sublogicOfSentence :: Sublogic -> Sentence -> Sublogic
sublogicOfSentence minimumSublogic sentence = case sentence of
  AF_THF_Annotated _ -> leastUpperBound minimumSublogic THF
  AF_TFX_Annotated _ -> leastUpperBound minimumSublogic THF
  AF_TFF_Annotated _ -> leastUpperBound minimumSublogic TFF
  AF_TCF_Annotated _ -> leastUpperBound minimumSublogic TFF
  AF_FOF_Annotated _ -> leastUpperBound minimumSublogic FOF
  AF_CNF_Annotated _ -> leastUpperBound minimumSublogic CNF
  AF_TPI_Annotated _ -> leastUpperBound minimumSublogic THF

sublogicOfSymbol :: Sublogic -> Symbol -> Sublogic
sublogicOfSymbol minimumSublogic _ = minimumSublogic

sublogicOfSign :: Sublogic -> Sign -> Sublogic
sublogicOfSign minimumSublogic sign = case () of
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
  _ -> minimumSublogic

sublogicOfMorphism :: Sublogic -> Morphism -> Sublogic
sublogicOfMorphism minimumSublogic morphism =
  leastUpperBound
    (sublogicOfSign minimumSublogic $ domOfDefaultMorphism morphism)
    (sublogicOfSign minimumSublogic $ codOfDefaultMorphism morphism)


{- ----------------------------------------------------------------------------
 - Determine projections
---------------------------------------------------------------------------- -}
-- TODO: complete the projections

projectSublogicBasicSpec :: Sublogic -> BASIC_SPEC -> BASIC_SPEC
projectSublogicBasicSpec _ basicSpec = basicSpec

projectSublogicSign :: Sublogic -> Sign -> Sign
projectSublogicSign _ sign = sign

projectSublogicSentence :: Sublogic -> Sentence -> Sentence
projectSublogicSentence _ sentence = sentence

projectSublogicMorphism :: Sublogic -> Morphism -> Morphism
projectSublogicMorphism _ morphism = morphism


projectSublogicMUnit :: Sublogic -> () -> Maybe ()
projectSublogicMUnit _ = Just

projectSublogicMSymbol :: Sublogic -> Symbol -> Maybe Symbol
projectSublogicMSymbol _ symbol = Just symbol
