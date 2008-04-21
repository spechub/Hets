{-# OPTIONS -fglasgow-exts #-}

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
