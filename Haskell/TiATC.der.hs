{-# OPTIONS -w #-}
{- |
Module      :  $Header$
Description :  ShATermConvertible instances
Copyright   :  (c) Christian Maeder, Uni Bremen 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

some 'ShATermConvertible' instances based on
the generated instances in "Haskell.ATC_Haskell".
-}

module Haskell.TiATC() where

import Common.ATerm.Lib
import Common.BinaryInstances
import TiTypes
import TiKinds
import TiInstanceDB
import PropSyntaxRec
import Haskell.HatParser(HsDecls(..))
import Haskell.HatAna(Sign(..))
import Haskell.ATC_Haskell()
import Data.Typeable

{-! for Qual derive : Typeable !-}
{-! for Scheme derive : Typeable !-}
{-! for Typing derive : Typeable !-}
{-! for TypeInfo derive : Typeable !-}
{-! for Subst derive : Typeable !-}
{-! for Kind derive : Typeable !-}
{-! for KVar derive : Typeable !-}
{-! for KindConstraint derive : Typeable !-}
{-! for InstEntry derive : Typeable !-}
{-! for HsDeclI derive : Typeable !-}
{-! for AssertionI derive : Typeable !-}
{-! for PredicateI derive : Typeable !-}
{-! for HsExpI derive : Typeable !-}
{-! for HsDecls derive : Typeable !-}
{-! for Sign derive : Typeable !-}

{-! for Qual derive : ShATermConvertible !-}
{-! for Scheme derive : ShATermConvertible !-}
{-! for Typing derive : ShATermConvertible !-}
{-! for TypeInfo derive : ShATermConvertible !-}
{-! for Subst derive : ShATermConvertible !-}
{-! for Kind derive : ShATermConvertible !-}
{-! for KVar derive : ShATermConvertible !-}
{-! for KindConstraint derive : ShATermConvertible !-}
{-! for InstEntry derive : ShATermConvertible !-}
{-! for HsDeclI derive : ShATermConvertible !-}
{-! for AssertionI derive : ShATermConvertible !-}
{-! for PredicateI derive : ShATermConvertible !-}
{-! for HsExpI derive : ShATermConvertible !-}
{-! for HsDecls derive : ShATermConvertible !-}
{-! for Sign derive : ShATermConvertible !-}

{-! for Qual derive : Binary !-}
{-! for Scheme derive : Binary !-}
{-! for Typing derive : Binary !-}
{-! for TypeInfo derive : Binary !-}
{-! for Subst derive : Binary !-}
{-! for Kind derive : Binary !-}
{-! for KVar derive : Binary !-}
{-! for KindConstraint derive : Binary !-}
{-! for InstEntry derive : Binary !-}
{-! for HsDeclI derive : Binary !-}
{-! for AssertionI derive : Binary !-}
{-! for PredicateI derive : Binary !-}
{-! for HsExpI derive : Binary !-}
{-! for HsDecls derive : Binary !-}
{-! for Sign derive : Binary !-}
