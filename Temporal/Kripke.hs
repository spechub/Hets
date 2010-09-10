{-# OPTIONS -fglasgow-exts #-}
{- |
Module      :  $Header$
Copyright   :  (c) Klaus Hartke, Uni Bremen 2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  non-portable (MPTC-FD)

-}

module Kripke where

import Data.Set as Set



{------------------------------------------------------------------------------}
{-                                                                            -}
{-  Kripke Structure                                                          -}
{-                                                                            -}
{------------------------------------------------------------------------------}

class Kripke k a s | k -> a s where
    states  :: k -> Set s
    initial :: k -> Set s
    next    :: k -> s -> Set s
    labels  :: k -> s -> Set a



{------------------------------------------------------------------------------}
