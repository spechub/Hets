{- |
Module      :  $Header$
Description :  automatic proofs in the development graph calculus
Copyright   :  (c) Jorina F. Gerken, Mossakowski, Luettich, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
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

import Proofs.Global
import Proofs.Local
import Proofs.HideTheoremShift
import Proofs.TheoremHideShift

import Static.DevGraph
import Static.History

import Common.LibName
import qualified Common.Lib.SizedList as SizedList

import qualified Data.Map as Map
import Data.Graph.Inductive.Graph
import Common.Result

automaticFromList :: LibName ->  [LEdge DGLinkLab] -> LibEnv -> LibEnv
automaticFromList ln ls libEnv =
  let x = automaticRecursiveFromList ln libEnv ls
      y = localInferenceFromList ln ls x
  in y

noChange :: LibEnv -> LibEnv -> Bool
noChange oldLib newLib = and $ Map.elems $ Map.intersectionWith
  (\ a b -> SizedList.null . snd $ splitHistory a b) oldLib newLib

automaticRecursiveFromList :: LibName -> LibEnv -> [LEdge DGLinkLab]
                           -> LibEnv
automaticRecursiveFromList ln proofstatus ls =
  let auxProofstatus = automaticApplyRulesToGoals ln ls proofstatus
                                                  rulesWithGoals
  in if noChange proofstatus auxProofstatus then auxProofstatus
     else automaticRecursiveFromList ln auxProofstatus ls

{- | automatically applies all rules to the library
   denoted by the library name of the given proofstatus-}
automatic :: LibName -> LibEnv -> LibEnv
automatic ln le = let nLib = localInference ln $ automaticRecursive 49 ln le in
  Map.intersectionWith (\ odg ndg ->
      groupHistory odg (DGRule "automatic") ndg) le nLib

{- | applies the rules recursively until no further changes can be made -}
automaticRecursive :: Int -> LibName -> LibEnv -> LibEnv
automaticRecursive count ln proofstatus =
  let auxProofstatus = automaticApplyRules ln proofstatus
  in if noChange proofstatus auxProofstatus || count < 1 then auxProofstatus
     else automaticRecursive (count - 1) ln auxProofstatus

wrapTheoremHideShift :: LibName -> LibEnv -> LibEnv
wrapTheoremHideShift ln libEnv =
 case maybeResult $ theoremHideShift ln libEnv of
   Nothing -> libEnv
   Just libEnv' -> libEnv'

-- | list of rules to use
rules :: [LibName -> LibEnv -> LibEnv]
rules =
    [ automaticHideTheoremShift
    , globDecomp
    , wrapTheoremHideShift
    ]

rulesWithGoals :: [LibName -> [LEdge DGLinkLab] -> LibEnv -> LibEnv]
rulesWithGoals =
            [automaticHideTheoremShiftFromList
            , locDecompFromList
            , globDecompFromList
            , globSubsumeFromList
            ]

automaticApplyRulesToGoals :: LibName -> [LEdge DGLinkLab] -> LibEnv ->
                 ([LibName -> [LEdge DGLinkLab] -> LibEnv -> LibEnv])
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
automaticApplyRules :: LibName -> LibEnv -> LibEnv
automaticApplyRules ln = foldl (.) id $ map (\ f -> f ln) rules
