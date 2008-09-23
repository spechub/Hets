{- |
Module      :  $Header$
Description :  automatic proofs in the development graph calculus
Copyright   :  (c) Jorina F. Gerken, Mossakowski, Luettich, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  ken@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(Logic)

automatic proofs in development graphs.
   Follows Sect. IV:4.4 of the CASL Reference Manual.
-}

{-
   References:

   T. Mossakowski, S. Autexier and D. Hutter:
   Extending Development Graphs With Hiding.
   H. Hussmann (ed.): Fundamental Approaches to Software Engineering 2001,
   Lecture Notes in Computer Science 2029, p. 269-283,
   Springer-Verlag 2001.

-}

module Proofs.Automatic (automatic, automaticFromList) where

import Proofs.StatusUtils
import Proofs.Global
import Proofs.Local
import Proofs.HideTheoremShift

import Static.DevGraph
import Common.LibName

import qualified Data.Map as Map
import Data.Graph.Inductive.Graph
import Data.Maybe (fromJust)


automaticFromList :: LIB_NAME ->  [LEdge DGLinkLab] -> LibEnv -> LibEnv
automaticFromList ln ls libEnv=
  let x = automaticRecursiveFromList ln 0 libEnv ls
      y = localInferenceFromList ln ls x
      z = mergeHistories 0 2 y
  in fromJust z

automaticRecursiveFromList :: LIB_NAME -> Int -> LibEnv -> [LEdge DGLinkLab]
                           -> LibEnv
automaticRecursiveFromList ln cnt proofstatus ls =
  let auxProofstatus = automaticApplyRulesToGoals ln ls proofstatus
                                                  rulesWithGoals
      finalProofstatus = mergeHistories cnt noRulesWithGoals auxProofstatus
  in case finalProofstatus of
     Nothing -> proofstatus
     Just p -> automaticRecursiveFromList ln 1 p ls

{- | automatically applies all rules to the library
   denoted by the library name of the given proofstatus-}
automatic :: LIB_NAME -> LibEnv -> LibEnv
automatic ln = fromJust . mergeHistories 0 2 .
            localInference ln . automaticRecursive ln 0

{- | applies the rules recursively until no further changes can be made -}
automaticRecursive :: LIB_NAME -> Int -> LibEnv -> LibEnv
automaticRecursive ln cnt proofstatus =
  let auxProofstatus = automaticApplyRules ln proofstatus
      finalProofstatus = mergeHistories cnt noRules auxProofstatus
  in case finalProofstatus of
    Nothing -> proofstatus
    Just p -> automaticRecursive ln 1 p

-- | list of rules to use
rules :: [LIB_NAME -> LibEnv -> LibEnv]
rules =
    [automaticHideTheoremShift
    , locDecomp
    , globDecomp
    , globSubsume
         -- , theoremHideShift
    ]

-- | number of rules
noRules :: Int
noRules = length rules

rulesWithGoals :: [LIB_NAME -> [LEdge DGLinkLab] -> LibEnv -> LibEnv]
rulesWithGoals =
            [automaticHideTheoremShiftFromList
            , locDecompFromList
            , globDecompFromList
            , globSubsumeFromList
            ]

noRulesWithGoals :: Int
noRulesWithGoals = length rulesWithGoals

automaticApplyRulesToGoals :: LIB_NAME -> [LEdge DGLinkLab] -> LibEnv ->
                 ([LIB_NAME -> [LEdge DGLinkLab] -> LibEnv -> LibEnv])
                 ->LibEnv
automaticApplyRulesToGoals ln ls libEnv ll=
 case ll of
     [] -> libEnv
     f:l-> let nwLibEnv= f ln ls libEnv
               dgraph = lookupDGraph ln nwLibEnv
               updateList = filter
                             (\(_,_,lp) ->
                                case thmLinkStatus
                                      $ dgl_type lp of
                                 Just LeftOpen -> True
                                 _             -> False)
                                  $ labEdgesDG dgraph
           in automaticApplyRulesToGoals ln updateList nwLibEnv l

{- | sequentially applies all rules to the given proofstatus,
   ie to the library denoted by the library name of the proofstatus -}
automaticApplyRules :: LIB_NAME -> LibEnv -> LibEnv
automaticApplyRules ln = foldl (.) id $ map (\ f -> f ln) rules

{- | merges for every library the new history elements
   to one new history element -}
mergeHistories :: Int -> Int -> LibEnv -> Maybe LibEnv
mergeHistories cnt lenNewHistory libEnv =
  let (numChanges,newProofstatus) = mergeHistoriesAux cnt lenNewHistory
                                    (Map.keys libEnv) libEnv
  in if numChanges > 0 then
     Just newProofstatus
    else Nothing

{- | auxiliary method for mergeHistories:
   determined the library names and recursively applies mergeHistory -}
mergeHistoriesAux :: Int -> Int -> [LIB_NAME] -> LibEnv -> (Int, LibEnv)
mergeHistoriesAux _ _ [] proofstatus = (0, proofstatus)
mergeHistoriesAux cnt lenNewHistory (ln:list) proofstatus =
  let ps = mergeHistory cnt lenNewHistory ln proofstatus
  in case ps of
    Just newProofstatus -> let
      (i,finalProofstatus) = mergeHistoriesAux cnt lenNewHistory list
                             newProofstatus
      in (i+1,finalProofstatus)
    Nothing -> mergeHistoriesAux cnt lenNewHistory list proofstatus

{- | merges the new history elements of a single library
   to one new history elemebt-}
mergeHistory :: Int -> Int -> LIB_NAME -> LibEnv -> Maybe LibEnv
mergeHistory cnt lenNewHistory ln proofstatus =
  let history = lookupHistory ln proofstatus
      (newHistoryPart, oldHistory) = splitAt (lenNewHistory+cnt) history
  in if null (concatMap snd $ take lenNewHistory newHistoryPart)
        && cnt == 1 then
     Nothing
   else
    let (dgrules, changes) = concatHistoryElems (reverse newHistoryPart)
        newHistoryElem = (dgrules, removeContraryChanges changes)
        newHistory = newHistoryElem : oldHistory
    in Just $ Map.update (\ c -> Just c { proofHistory = newHistory })
       ln proofstatus

{- | concats the given history elements to one history element-}
concatHistoryElems :: [([DGRule],[DGChange])] -> ([DGRule],[DGChange])
concatHistoryElems [] = ([], [])
concatHistoryElems ((dgrules, changes) : elems) =
  (dgrules ++ fst (concatHistoryElems elems),
         changes ++ snd (concatHistoryElems elems))
