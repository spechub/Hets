{-
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2005
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

pretty print AS of CASL_DL in ASCII
-}

module CASL_DL.Print_AS where

-- import Common.Id
import Common.Lib.Pretty
import Common.PrettyPrint
import Common.PPUtils

import CASL_DL.AS_CASL_DL

			     
instance PrettyPrint DL_FORMULA where
    printText0 _ = text . show