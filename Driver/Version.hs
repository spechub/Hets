{- |
Module      :  $Header$
Description :  module for the hets version string
Copyright   :  (c) Uni-Bremen, DFKI 2012
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

generated version module of Hets

-}

module Driver.Version where

hets_version_numeric :: String
hets_version_numeric = "0.100.0"

hets_version :: String
hets_version =
  "The Heterogeneous Tool Set, version " ++ hets_version_numeric
