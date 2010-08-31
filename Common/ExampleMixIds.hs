{- |
Module      :  $Header$
Description :  standard mixfix identifier
Copyright   :  (c) Christian Maeder and DFKI Bremen 2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

mixfix identifiers for testing CASL's and HasCASL's mixfix analysis
-}

module Common.ExampleMixIds (stdOpsL, stdPreds, mkIds) where

import Common.Id
import Common.AnnoParser
import Common.Lexer
import qualified Data.Set as Set

stdOpsL :: [String]
stdOpsL =
  [ "__^__", "__*__", "__+__", "[__]","__div__","__mod__", "__rem__"
  , "__-__", "+__", "__E__", "__@@__", "[]", "__::__", "__:::__", "-__", "__!"
  , "____p", "q____","____x____", "{____}"
  , "repeat__until__", "while__do__od", "__none__but__", "__one__done"
  , "A[a[c,d],b]", "B[a[c,d],b]", "__B[a[c,d],b]__"
  , "a[c,d]", "__a[c,d]__", "A[a]", "A__B", "A__", "__[a]", "__p"
  , "__ --> __", "__{__}--__-->{__}__", "__[__]__", "[__]__", "__[__]" ]

stdPredsL :: [String]
stdPredsL =
  [ "__<__", "__<=__", "__>__", "__>=__", "__!=__", "__<>__"
  , "__/=__", "even__", "odd__", "__isEmpty", "__<=__<=__" ]

mkIds :: [String] -> Set.Set Id
mkIds = Set.fromList . map (parseString parseAnnoId)

stdPreds :: Set.Set Id
stdPreds = mkIds stdPredsL
