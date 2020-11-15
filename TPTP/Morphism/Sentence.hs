{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./TPTP/Morphism.hs
Description :  Symbol-related functions for TPTP.
Copyright   :  (c) Eugen Kuksa University of Magdeburg 2017
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Eugen Kuksa <kuksa@iks.cs.ovgu.de>
Stability   :  provisional
Portability :  non-portable (imports Logic)

Symbol-related functions for TPTP.
-}

module TPTP.Morphism.Sentence (symbolsOfSentence) where

import TPTP.Morphism
import TPTP.Sign as Sign
import TPTP.StaticAnalysis (signOfSentence)

import qualified Data.HashSet as Set

symbolsOfSentence :: Sentence -> Set.HashSet Symbol
symbolsOfSentence = symbolsOfSign . signOfSentence
