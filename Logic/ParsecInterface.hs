{-| 
   
Module      :  $Header$
Copyright   :  (c) Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   no longer used interface for Parsec parsers.
   Generates a parser as needed by Logic.hs
-}

module Logic.ParsecInterface
where

import Common.AnnoState

-- | don't set a new state  
toParseFun :: AParser a -> st -> AParser a  
toParseFun p _ = p
