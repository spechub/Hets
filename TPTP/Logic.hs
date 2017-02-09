{-# LANGUAGE CPP, MultiParamTypeClasses, TypeSynonymInstances
  , FlexibleInstances #-}
{- |
Module      :  ./TPTP/Logic.hs
Description :  Instance of class Logic for TPTP.
Copyright   :  (c) Eugen Kuksa University of Magdeburg 2017
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Eugen Kuksa <kuksa@iks.cs.ovgu.de>
Stability   :  provisional
Portability :  non-portable (imports Logic)

Instance of class Logic for TPTP.
-}

module TPTP.Logic where

import TPTP.AS hiding (TPTP)
import TPTP.ATC_TPTP ()
import TPTP.Morphism
import TPTP.Morphism.Sentence
import TPTP.Parser
import TPTP.Pretty
import TPTP.Sign
import TPTP.Sublogic as Sublogic
import TPTP.StaticAnalysis

import Common.DefaultMorphism
import Logic.Logic as Logic

import Data.Monoid
import qualified Data.Set as Set

data TPTP = TPTP deriving (Show, Ord, Eq)

instance Language TPTP
  where
    description _ =
      "The TPTP (Thousands of Problems for Theorem Provers) Language" ++
      "See http://www.cs.miami.edu/~tptp/"

instance Syntax TPTP BASIC_SPEC Symbol () ()
  where
    parse_basic_spec TPTP = Just parseBasicSpec

instance Monoid BASIC_SPEC where
    mempty = Basic_spec []
    mappend (Basic_spec l1) (Basic_spec l2) = Basic_spec $ l1 ++ l2

instance Sentences TPTP Sentence Sign Morphism Symbol
  where
    map_sen TPTP _ = return
    sym_of TPTP = singletonList . symbolsOfSign
    symsOfSen TPTP _ = Set.toList . symbolsOfSentence
    sym_name TPTP = symbolToId
    symKind TPTP = symbolTypeS
    print_named TPTP = printNamedSentence
    negation TPTP = negateSentence

instance StaticAnalysis TPTP BASIC_SPEC Sentence () () Sign Morphism Symbol ()
  where
    empty_signature TPTP = emptySign
    is_subsig TPTP _ _ = True
    subsig_inclusion TPTP = defaultInclusion
    basic_analysis TPTP = Just basicAnalysis
    signature_union TPTP = signatureUnionR

instance Logic TPTP Sublogic BASIC_SPEC Sentence () () Sign Morphism Symbol () ProofTree
  where
    stability _ = Testing
    provers TPTP = []


instance SublogicName Sublogic where
    sublogicName = Sublogic.sublogicName

instance SemiLatticeWithTop Sublogic where
    lub = leastUpperBound
    top = Sublogic.top


instance MinSublogic Sublogic () where
  minSublogic = sublogicOfUnit bottom

instance MinSublogic Sublogic BASIC_SPEC where
  minSublogic = sublogicOfBaiscSpec bottom

instance MinSublogic Sublogic Sentence where
  minSublogic = sublogicOfSentence bottom

instance MinSublogic Sublogic Symbol where
  minSublogic = sublogicOfSymbol bottom

instance MinSublogic Sublogic Sign where
  minSublogic = sublogicOfSign bottom

instance MinSublogic Sublogic Morphism where
  minSublogic = sublogicOfMorphism bottom


instance ProjectSublogic Sublogic BASIC_SPEC where
  projectSublogic = projectSublogicBasicSpec

instance ProjectSublogic Sublogic Sentence where
  projectSublogic = projectSublogicSentence

instance ProjectSublogic Sublogic Sign where
  projectSublogic = projectSublogicSign

instance ProjectSublogic Sublogic Morphism where
  projectSublogic = projectSublogicMorphism


instance ProjectSublogicM Sublogic () where
  projectSublogicM = projectSublogicMUnit

instance ProjectSublogicM Sublogic Symbol where
  projectSublogicM = projectSublogicMSymbol
