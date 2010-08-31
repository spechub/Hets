{- |
Module      :  $Header$
Description :  ShATermConvertible instances
Copyright   :  (c) Christian Maeder, Uni Bremen 2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (imports programatica modules)

'ShATermConvertible' instances for TiPropDecorate data types
-}

module Haskell.TiPropATC() where

import ATerm.Lib
import TiPropDecorate
import Haskell.TiDecorateATC()
import Data.Typeable

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
