{-# OPTIONS -fno-strictness #-}
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

'ShATermConvertible' instances for TiPropDecorate data types
-}

module Haskell.TiPropATC() where

import Common.ATerm.Lib
import TiPropDecorate
import Haskell.TiDecorateATC()
import ATC.Set()
import Common.DynamicUtils

{-! for TiDecls derive : Typeable !-}
{-! for TiDecl derive : Typeable !-}
{-! for TiAssertion derive : Typeable !-}
{-! for TiPredicate derive : Typeable !-}
{-! for OTiAssertion derive : Typeable !-}
{-! for TiExp derive : Typeable !-}

{-! for TiDecls derive : ShATermConvertible !-}
{-! for TiDecl derive : ShATermConvertible !-}
{-! for TiAssertion derive : ShATermConvertible !-}
{-! for TiPredicate derive : ShATermConvertible !-}
{-! for OTiAssertion derive : ShATermConvertible !-}
{-! for TiExp derive : ShATermConvertible !-}
