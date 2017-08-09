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

hetcats_version_numeric :: String
hetcats_version_numeric = "0.100.0"

hetcats_version :: String
hetcats_version =
  "The Heterogeneous Tool Set, version " ++ hetcats_version_numeric
