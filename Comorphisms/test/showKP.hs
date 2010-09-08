{- |
Module      :  $Header$
Copyright   :  (c) C. Maeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  non-portable (via imports)

-}

module Main where

import Comorphisms.KnownProvers

main :: IO ()
main = showAllKnownProvers
