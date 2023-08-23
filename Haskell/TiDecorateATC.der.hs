{-# LANGUAGE CPP, StandaloneDeriving, DeriveDataTypeable #-}
{- |
Module      :  ./Haskell/TiDecorateATC.der.hs
Description :  ShATermConvertible instances
Copyright   :  (c) Christian Maeder, Uni Bremen 2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (imports programatica modules)

'ShATermConvertible' instances for TiDecorate data types
-}

module Haskell.TiDecorateATC () where

import ATerm.Lib
import TiDecorate
import Haskell.ATC_Haskell ()
import Haskell.TiATC ()
import Data.Typeable

{-! for TiDecls derive : Typeable !-}
{-! for TiDecl derive : Typeable !-}
{-! for TiExp derive : Typeable !-}
{-! for TiPat derive : Typeable !-}

{-! for TiDecls derive : ShATermConvertible !-}
{-! for TiDecl derive : ShATermConvertible !-}
{-! for TiExp derive : ShATermConvertible !-}
{-! for TiPat derive : ShATermConvertible !-}
