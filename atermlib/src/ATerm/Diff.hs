{- |
Module      :  ./atermlib/src/ATerm/Diff.hs
Description :  compute the differences of two unshared ATerms
Copyright   :  (c) Klaus Luettich, Uni Bremen 2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (imports ATerm.Unshared)

Provides functions that calculate differences in unshared 'ATerm's.
-}

module ATerm.Diff (atDiff) where

import ATerm.Unshared
import Data.List

{- | all diferences between both terms are replaced by appropiate
placeholders (in @\<\>@) and the differing terms are added to the
list of ATerm as arguments to the function symbol @diff@. -}
--
{- /Note:
this function ignores annotions and the resulting ATerm does not
contain any annotation!/ -}

atDiff :: ATerm -> ATerm -> (ATerm, [ATerm])
atDiff a1@(AAppl s1 atl1 _) a2@(AAppl s2 atl2 _)
    | s1 == s2 && atl1 == atl2 = (AAppl s1 atl1 [], [])
    | s1 == s2 &&
      length atl1 == length atl2 =
          case atDiffL atl1 atl2 of
          (diffs, atl) -> (AAppl s1 atl [], diffs)
    | otherwise = (AAppl "<diff-appls>" [] [], [AAppl "diff" [a1, a2] []])
atDiff a1@(AInt i1 _) a2@(AInt i2 _)
    | i1 == i2 = (AInt i1 [], [])
    | otherwise = (AAppl "<diff-int>" [] [], [AAppl "diff" [a1, a2] []])
atDiff a1@(AList l1 _) a2@(AList l2 _)
    | l1 == l2 = (AList l1 [], [])
    | length l1 == length l2 =
        case atDiffL l1 l2 of
        (diffs, atl) -> (AList atl [], diffs)
    | otherwise = (AList [AAppl "<diff-lists>" [] []] [],
                   [AAppl "diff" [a1, a2] []])
atDiff a1 a2 = (AAppl "<diff-types>" [] [], [AAppl "diff" [a1, a2] []])

atDiffL :: [ATerm] -> [ATerm] -> ([ATerm], [ATerm])
atDiffL atl1 atl2 =
    mapAccumL (\ acc (ia1, ia2) ->
                  case atDiff ia1 ia2 of
                  (at, diffs) -> (acc ++ diffs, at)) [] (zip atl1 atl2)
