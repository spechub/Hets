{- |
Module      :  $Header$
Copyright   :  (c) Mingyi Liu and Till Mossakowski and Uni Bremen 2004-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  xinga@tzi.de
Stability   :  provisional
Portability :  non-portable (mutual recursive module)

an interface file for resolving recursive modules
-}

module CASL.CCC.FreeTypes where

import CASL.Sign
import CASL.Morphism
import CASL.AS_Basic_CASL -- FORMULA

import Common.AS_Annotation
import Common.Result

checkFreeType :: (Sign () (),[Named (FORMULA ())]) -> Morphism () () ()
              -> [Named (FORMULA ())] -> Result (Maybe (Bool,[FORMULA ()]))
