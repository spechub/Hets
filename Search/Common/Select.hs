{- |
Module      :  $Header$
Description :  Logic independent retrieval functionality
Copyright   :  (c) Immanuel Normann, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  inormann@jacobs-university.de
Stability   :  provisional
Portability :  portable
-}

module Search.Common.Select where

import Data.List as L
import Data.Set as S
import Data.Map as M (Map, map, keys, lookup, filter, fromList, singleton, union)
import Search.Utils.SetMap as SM --(fromListSetValues)
import Search.Utils.List
import Database.HaskellDB
import Database.HaskellDB.DriverAPI
import Database.HaskellDB.HDBRec
import Search.DB.Connection
import Search.DB.FormulaDB.Profile


type Skel = String
type TheoryName = String
type ParamString = String
type LineNr = Int
type AxiomNr = Int -- number of different axioms in a source theory
type Renaming a = M.Map a a
type LineMap = M.Map Int Int
type ProfileMorphism a = (Renaming a, LineMap)

-- theory = "alg_1__t10_alg_1.dfg"
{-
queryProfileMoprhisms file =
    do sourceList <- getSourceAxiomProfiles file
       let 
-}
{-
  Matching

-}
profileMorphisms :: (Read p, Ord p, Ord t) =>
                     [(t, [p], LineNr)] 
                         -> Map t (Set ([p], LineNr)) 
                         -> [(Renaming p, LineMap)]
profileMorphisms sourceProfileList db =
    case sequence (L.map (profileMorphism db) sourceProfileList)
    of (Just listOfProfileMorphs) -> mergeProfileMorphs listOfProfileMorphs
       Nothing -> []

mergeProfileMorphs :: (Ord p, Read p) => [[(Renaming p, LineMap)]]
                   -> [(Renaming p, LineMap)]
mergeProfileMorphs lst = foldr mergeProfilePair [] lst


mergeProfilePair :: (Ord p, Read p) => [(Renaming p, LineMap)]
                 -> [(Renaming p, LineMap)]
                 -> [(Renaming p, LineMap)]
mergeProfilePair ps1 ps2 = allJust [merge p1 p2 | p1 <- ps1, p2 <- ps2]
    where merge (r1,l1) (r2,l2) =
              case maybeUnion r1 r2
              of (Just r) -> Just (r, M.union l1 l2)
                 Nothing -> Nothing

profileMorphism db (skel,ps,line) = 
    case M.lookup skel db
    of (Just targetProfileSet) -> formulaMorphismSet (ps,line) targetProfileSet


formulaMorphismSet :: (Ord p, Read p) => ([p],LineNr)
                   -> (S.Set ([p],LineNr))
                   -> Maybe [(Renaming p, LineMap)]
formulaMorphismSet sourceProfile targetProfileSet =
    sequence $ S.toList $ S.map (formulaMorphism sourceProfile) targetProfileSet

formulaMorphism :: (Ord p, Read p) => ([p],LineNr) -> ([p],LineNr)
                -> Maybe (Renaming p, LineMap)
formulaMorphism (p1,l1) (p2,l2) =
    case constructRenaming p1 p2
    of (Just renaming) -> Just (renaming, M.singleton l1 l2)
       _ -> Nothing

constructRenaming :: (Ord p, Read p) => [p] -> [p] -> Maybe (Renaming p)
constructRenaming lst1 lst2 = SM.fromList $ zip lst1 lst2


{-
  Database Access
-}

{- for SPASS:
fetchTargetProfiles :: TheoryName -> Set LineNr -> IO [([String], LineNr)]

x :: TheoryName -> Set LineNr -> IO [(Skel, ([String], LineNr))]
x = fetchTargetProfiles

fetchTargetProfiles :: (Ord a, Read a) => TheoryName -> Set LineNr -> IO [(Skel, ([a], LineNr))]
fetchTargetProfiles tn lnrs =
fetchTargetProfiles sourceSkelInstanceMap
    let q = do t <- table profile  -- the query
	       restrict (t!file .==. constant tn .&&.
                         _in (t!line) (L.map constant (S.toList lnrs)))
	       project (skeleton_md5 << t!skeleton_md5 #
                        parameter << t!parameter #
                        line << t!line)
        recToTuple_skel_parameter_line rec = (s, (read p,l))  -- translate Recs to pairs
            where (RecCons s (RecCons p (RecCons l _))) = rec RecNil
    in do recs <- myQuery q
          return $ L.map recToTuple_skel_parameter_line recs

-}

allTargetCandidates :: [Skel] -> IO (Map TheoryName (Map Skel (Set LineNr)))
allTargetCandidates skels = -- todo: skels should be Set too.
    let q = do t <- table profile  -- the query
	       restrict (_in (t!skeleton_md5) (L.map constant skels))
	       project (file << t!file # skeleton_md5 << t!skeleton_md5 # line << t!line)
        recToTuple_file_skel rec = (theory,(skel, line))  -- translate Recs to pairs
            where (RecCons theory (RecCons skel (RecCons line _))) = rec RecNil
        theoryToSkelLineSet recs = fromListSetValues $ L.map recToTuple_file_skel recs
        comprisesAllSkels skelLineSet = ((S.size $ S.map fst skelLineSet) == (length skels))
        relToMap = fromListSetValues . S.toList -- todo: should be improved w.r.t efficiency
    in do recs <- myQuery q
          return $ M.map relToMap $ M.filter comprisesAllSkels (theoryToSkelLineSet recs)
-- todo: sorting by theory should be performed by the database


{-
  Query File Access
-}

getSourceAxiomProfiles :: (Ord a, Read a) => FilePath -> [(Skel,([a],LineNr))]
getSourceAxiomProfiles = undefined
{-
getSourceAxiomProfiles file = zip md5s lines -- for testing
    where md5s = ["1a8c5f73411bbd689bff1d9306b9da3b", "0df802cf17eb339f0bbcdd2d86c06506", "87929a4736dd0d152b4dde3c29ea213e"]
          lines = [1,2,3]
-}

{-
getAxioms dir file =
    getProfiles dir file >>= (sortProfiles . 
                              removeDuplicateProfiles . 
                              removeTrueAtoms . 
                              removeTheorems)
-}
-- ** Filter Functions
{- |
   

removeTrueAtoms :: [Profile t f (Skeleton c) [p]] -> [Profile t f (Skeleton c) [p]]
removeTrueAtoms profiles = filter isNotTrueAtom profiles
    where isNotTrueAtom (Profile _ _ (Const TrueAtom []) _) = False
	  isNotTrueAtom _ = True

removeTheorems :: [Profile t f (Skeleton c) [p]] -> [Profile t f (Skeleton c) [p]]
removeTheorems  profiles = filter isNotAxiom profiles
    where isNotAxiom = undefined -- todo!!!
-}