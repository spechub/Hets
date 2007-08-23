{- |
Module      :  $Header$
Description :  generated Typeable, ShATermConvertible instances
Copyright   :  (c) Hendrik Iben, Uni Bremen 2005-2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  hiben@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Instances for ATerm-Conversion of OMDoc.
-}
module OMDoc.OMDocExt where

import OMDoc.OMDocInterface
import OMDoc.ATerm()
import Data.Typeable
import Common.ATerm.Lib

{-! for OMDoc.OMDocInterface.SymbolRole derive : Typeable !-}
{-! for OMDoc.OMDocInterface.Symbol derive : Typeable !-}
{-! for OMDoc.OMDocInterface.Type derive : Typeable !-}
{-! for OMDoc.OMDocInterface.OMDocMathObject derive : Typeable !-}
{-! for OMDoc.OMDocInterface.OMObject derive : Typeable !-}
{-! for OMDoc.OMDocInterface.OMElement derive : Typeable !-}
{-! for OMDoc.OMDocInterface.OMSymbol derive : Typeable !-}
{-! for OMDoc.OMDocInterface.OMSimpleVariable derive : Typeable !-}
{-! for OMDoc.OMDocInterface.OMInteger derive : Typeable !-}
{-! for OMDoc.OMDocInterface.OMBase64 derive : Typeable !-}
{-! for OMDoc.OMDocInterface.OMString derive : Typeable !-}
{-! for OMDoc.OMDocInterface.OMFloat derive : Typeable !-}
{-! for OMDoc.OMDocInterface.OMApply derive : Typeable !-}
{-! for OMDoc.OMDocInterface.OMBind derive : Typeable !-}
{-! for OMDoc.OMDocInterface.OMError derive : Typeable !-}
{-! for OMDoc.OMDocInterface.OMAttribution derive : Typeable !-}
{-! for OMDoc.OMDocInterface.OMReference derive : Typeable !-}
{-! for OMDoc.OMDocInterface.OMBindingVariables derive : Typeable !-}
{-! for OMDoc.OMDocInterface.OMVariable derive : Typeable !-}
{-! for OMDoc.OMDocInterface.OMAttributionPart derive : Typeable !-}
{-! for OMDoc.OMDocInterface.Morphism derive : Typeable !-}
{-! for OMDoc.OMDocInterface.MText derive : Typeable !-}
{-! for OMDoc.OMDocInterface.Theory derive : Typeable !-}
{-! for OMDoc.OMDocInterface.Presentation derive : Typeable !-}
{-! for OMDoc.OMDocInterface.Use derive : Typeable !-}
{-! for OMDoc.OMDocInterface.Constitutive derive : Typeable !-}
{-! for OMDoc.OMDocInterface.Axiom derive : Typeable !-}
{-! for OMDoc.OMDocInterface.Definition derive : Typeable !-}
{-! for OMDoc.OMDocInterface.ADT derive : Typeable !-}
{-! for OMDoc.OMDocInterface.Imports derive : Typeable !-}
{-! for OMDoc.OMDocInterface.CMP derive : Typeable !-}
{-! for OMDoc.OMDocInterface.FMP derive : Typeable !-}
{-! for OMDoc.OMDocInterface.SortDef derive : Typeable !-}
{-! for OMDoc.OMDocInterface.Recognizer derive : Typeable !-}
{-! for OMDoc.OMDocInterface.Insort derive : Typeable !-}
{-! for OMDoc.OMDocInterface.Constructor derive : Typeable !-}
{-! for OMDoc.OMDocInterface.SortType derive : Typeable !-}
{-! for OMDoc.OMDocInterface.Conservativity derive : Typeable !-}
{-! for OMDoc.OMDocInterface.ImportsType derive : Typeable !-}
{-! for OMDoc.OMDocInterface.Assumption derive : Typeable !-}
{-! for OMDoc.OMDocInterface.Conclusion derive : Typeable !-}
{-! for OMDoc.OMDocInterface.Inclusion derive : Typeable !-}

{-! for OMDoc.OMDocInterface.SymbolRole derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.Symbol derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.Type derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.OMDocMathObject derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.OMObject derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.OMElement derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.OMSymbol derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.OMSimpleVariable derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.OMInteger derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.OMBase64 derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.OMString derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.OMFloat derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.OMApply derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.OMBind derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.OMError derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.OMAttribution derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.OMReference derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.OMBindingVariables derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.OMVariable derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.OMAttributionPart derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.Morphism derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.MText derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.Theory derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.Presentation derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.Use derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.Constitutive derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.Axiom derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.Definition derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.ADT derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.Imports derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.CMP derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.FMP derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.SortDef derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.Recognizer derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.Insort derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.Constructor derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.SortType derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.Conservativity derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.ImportsType derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.Assumption derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.Conclusion derive : ShATermConvertible !-}
{-! for OMDoc.OMDocInterface.Inclusion derive : ShATermConvertible !-}
