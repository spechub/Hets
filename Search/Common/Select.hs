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
import Data.Map as M hiding ((!))
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
class Retrievable p where
    getSourceAxiomProfiles :: FilePath -> IO [(Skel,([p],LineNr))]


queryProfileMorphisms :: (Retrievable p, Ord p, Read p) =>
                         FilePath -> IO [(TheoryName, [(Renaming p, LineMap)])]
queryProfileMorphisms file =
    do sourceList <- getSourceAxiomProfiles file 
       targetCandidates <- allTargetCandidates (L.map fst sourceList)
       mapM (showResults sourceList) (M.toList targetCandidates)

showResults :: (Ord p, Read p) =>
               [(Skel, ([p], LineNr))]
               -> (String, Map Skel (Set ([p], LineNr)))
               -> IO (String, [(Renaming p, LineMap)])
showResults sourceList (targetTheory,tMap) =
    do putStrLn targetTheory
       return (targetTheory,profileMorphism sourceList tMap)


{-
  Matching
-}


{- |
   profileMorphism finds all theory morphisms from profiles of a source theory
   to profiles in a target theory.
-}
profileMorphism :: (Ord p, Read p) =>
                   [(Skel,([p], LineNr))] -> M.Map Skel (S.Set ([p], LineNr)) -> [(Renaming p, LineMap)]
profileMorphism sourceProfiles targetProfileMap =
    foldr merge [] (L.map matchList' sourceProfiles)
        where matchList' (s,sourceProfile) = 
                  case M.lookup s targetProfileMap
                  of (Just targetProfiles) -> matchList (S.toList targetProfiles) sourceProfile
                     Nothing -> []

merge :: (Ord p, Read p) => [(Renaming p, LineMap)]
                 -> [(Renaming p, LineMap)]
                 -> [(Renaming p, LineMap)]
merge ps1 ps2 = allJust [merge' p1 p2 | p1 <- ps1, p2 <- ps2]
    where merge' (r1,l1) (r2,l2) =
              case maybeUnion r1 r2
              of (Just r) -> Just (r, M.union l1 l2)
                 Nothing -> Nothing

{- |
   matchList takes a single source pair and a set of target pairs
   and returns (Just) a renaming together with a line number mapping.
-}
matchList :: (Ord p, Read p) =>
            [([p], LineNr)] -> ([p], LineNr) -> [(Renaming p, LineMap)]
matchList targetProfiles sourceProfile =
    foldr justInsert [] (L.map (match sourceProfile) targetProfiles)
        where justInsert Nothing lst = lst
              justInsert (Just x) lst = x:lst

{- |
   match takes two pairs and returns (Just) 
   a renaming of parameters and a line number association
   if the pairs match and Nothing otherwise.
   Each pair has a list of parameter as first component
   and a line number as second. Each pair represents formula
   whose skeleton is supposed to be identical.
   The pairs match iff their parameter do (s. 'constructRenaming').
-}
match :: (Ord p, Read p) => ([p],LineNr) -> ([p],LineNr)
                -> Maybe (Renaming p, LineMap)
match (p1,l1) (p2,l2) =
    case constructRenaming p1 p2
    of (Just renaming) -> Just (renaming, M.singleton l1 l2)
       _ -> Nothing

{- |
   constructRenaming takes two lists of parameters and returns (Just) a pointwise
   mapping between these lists if this is consistently possible.
   Otherwise it returns Nothing.
-}
constructRenaming :: (Ord p, Read p) => [p] -> [p] -> Maybe (Renaming p)
constructRenaming lst1 lst2 = SM.fromList $ zip lst1 lst2


{-
  Database Access
-}


{- |
   allTargetCandidates takes a list of skeletons and retrieves from the database
   target theories
-}
allTargetCandidates :: (Ord p, Read p) => 
                       [Skel] -> IO (Map TheoryName (Map Skel (Set ([p], LineNr))))
allTargetCandidates skels = 
    do triples <- matchSkeleton skels
       return $ (M.map fromSetSetValues (M.filter comprisesAllSkels (fromListSetValues triples)))
           where comprisesAllSkels skelLineSet = 
                     ((S.size $ S.map fst skelLineSet) == (length skels))


{- |
   matchSkeleton takes a list of skeletons and retrieves from the database all
   datasets whose skeleton matches one of the input list.
   (this function is only used in 'allTargetCandidates')
-}
matchSkeleton :: (Ord p, Read p) => [Skel] -> IO [(TheoryName, (Skel, ([p], LineNr)))]
matchSkeleton skels =
    let q = do t <- table profile  -- the query
	       restrict (_in (t!skeleton_md5) (L.map constant skels))
	       project (file << t!file # skeleton_md5 << t!skeleton_md5 # 
                        parameter << t!parameter # line << t!line)
        recToTuple rec = (theory,(skel, (read parameter, line)))
            where (RecCons theory (RecCons skel (RecCons parameter (RecCons line _)))) = 
                      rec RecNil
    in do recs <- myQuery q
          return $ L.map recToTuple recs


{-
  Query File Access
-}


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