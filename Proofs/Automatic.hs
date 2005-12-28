{- |
Module      :  $Header$
Copyright   :  (c) Jorina F. Gerken, Till Mossakowski, Klaus Lüttich, Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  jfgerken@tzi.de
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

todo in general:

Order of rule application: try to use local links induced by %implies
for subsumption proofs (such that the %implied formulas need not be
re-proved)

Integrate stuff from Saarbrücken
Add proof status information

 what should be in proof status:

- proofs of thm links according to rules
- cons, def and mono annos, and their proofs

-}

module Proofs.Automatic (automatic) where

import Static.DevGraph

import qualified Common.Lib.Map as Map

import Syntax.AS_Library
import Syntax.Print_AS_Library()

import Proofs.StatusUtils
import Proofs.Global
import Proofs.Local
import Proofs.HideTheoremShift

{- todo: implement apply for GlobDecomp and Subsumption
   the list of DGChage must be constructed in parallel to the
   new DGraph -}
applyRule :: DGRule -> DGraph -> Maybe ([DGChange],DGraph)
applyRule = error "Proofs.hs:applyRule"

{- automatically applies all rules to the library
   denoted by the library name of the given proofstatus-}
automatic :: ProofStatus -> ProofStatus
automatic = automaticRecursive 0

{- applies the rules recursively until no further changes can be made -}
automaticRecursive :: Int -> ProofStatus -> ProofStatus
automaticRecursive cnt proofstatus =
  let auxProofstatus = automaticApplyRules proofstatus
      finalProofstatus = mergeHistories cnt auxProofstatus
  in case finalProofstatus of
    Nothing -> proofstatus
    Just p -> automaticRecursive 1 p

{- sequentially applies all rules to the given proofstatus,
   ie to the library denoted by the library name of the proofstatus -}
automaticApplyRules :: ProofStatus -> ProofStatus
automaticApplyRules =
  automaticHideTheoremShift
  . locDecomp
  . localInference
  . globDecomp
  . globSubsume
   -- . theoremHideShift

{- merges for every library the new history elements
   to one new history element -}
mergeHistories :: Int -> ProofStatus -> Maybe ProofStatus
mergeHistories cnt proofstatus@(ln,libEnv,_) =
  let (numChanges,newProofstatus) = mergeHistoriesAux cnt
                                    (Map.keys libEnv) proofstatus
  in if (numChanges > 0) then
     Just $ changeCurrentLibName ln newProofstatus
    else Nothing

{- auxiliary method for mergeHistories:
   determined the library names and recursively applies mergeHistory -}
mergeHistoriesAux :: Int -> [LIB_NAME] -> ProofStatus -> (Int,ProofStatus)
mergeHistoriesAux _ [] proofstatus = (0, proofstatus)
mergeHistoriesAux cnt (ln:list) proofstatus =
  let ps = mergeHistory cnt (changeCurrentLibName ln proofstatus)
  in case ps of
    Just newProofstatus -> let
      (i,finalProofstatus) = mergeHistoriesAux cnt list newProofstatus
      in (i+1,finalProofstatus)
    Nothing -> mergeHistoriesAux cnt list proofstatus

{- merges the new history elements of a single library
   to one new history elemebt-}
mergeHistory :: Int -> ProofStatus -> Maybe ProofStatus
mergeHistory cnt proofstatus@(ln,libEnv,historyMap) =
  let history = lookupHistory ln proofstatus
--      dgraph = lookupDGraph ln proofstatus
      (newHistoryPart, oldHistory) = splitAt (5+cnt) history
  in if null (concatMap snd $ take 5 newHistoryPart) && cnt == 1 then
     Nothing
   else
    let (rules, changes) = concatHistoryElems (reverse newHistoryPart)
        newHistoryElem = (rules, removeContraryChanges changes)
        newHistory = newHistoryElem:oldHistory
    in Just (ln, libEnv, Map.insert ln newHistory historyMap)

{- concats the given history elements to one history element-}
concatHistoryElems :: [([DGRule],[DGChange])] -> ([DGRule],[DGChange])
concatHistoryElems [] = ([], [])
concatHistoryElems ((rules, changes) : elems) =
  (rules ++ fst (concatHistoryElems elems),
         changes ++ snd (concatHistoryElems elems))
