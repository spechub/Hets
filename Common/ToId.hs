{- |
Module      :  $Header$
Copyright   :  (c) T.Mossakowski, C.Maeder and Uni Bremen 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

converting (ie. kif) strings to CASL identifiers
-}

module Common.ToId where

import Common.Id
import Common.ProofUtils
import Common.Token

-- todo: check for CASL keywords and legal underline words

-- | convert 
toId :: String -> Id
toId s = mkId [mkSimpleId s]


