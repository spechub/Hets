{- |
Module      :  $Header$
Description :  Consistent many to many formulae matching
Copyright   :  (c) Immanuel Normann, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  inormann@jacobs-university.de
Stability   :  provisional
Portability :  portable
-}
module Search.Common.Matching where

import Data.List (nub,nubBy)
import qualified Data.Map as M
import Search.Utils.List (isRightUnique,filterNeq)

data Profile t fid sid p =
    Profile 
    { theory :: t,       -- ^ 't' is the theory where the profile belongs to
      formulaId :: fid,  -- ^ 'fid' is the id of the original formula relative to the theory 't'
      skeleton :: sid, -- ^ 'sid' the skeleton (or an representative id); i.e. the abstracted formula resulting from normalization
      parameter :: [p]   -- ^ '[p]' are the corresponding formula parameter
    } deriving (Eq, Ord, Show)

type ProfileMorphism s p = (FormulaIdMap s,ParameterMap p)
type FormulaIdMap fid = M.Map fid fid -- from source to target
type ParameterMap p = M.Map p p -- from source to target

-- ** Finding Morphisms between List of Profiles

profileMorphs :: (Eq sid,Ord t,Ord fid,Ord p)
                  => [Profile t fid sid p]   -- ^ the list of source profiles
                      -> [Profile t fid sid p]   -- ^ the list of target profiles
                      -> M.Map t [ProfileMorphism fid p] -- ^ list of all morphisms from the source to the target
profileMorphs sourceProfiles targetProfiles =
    M.map (profileMorphs1 sourceProfiles) (assignProfilesToTheories targetProfiles)

{- |
   assignProfilesToTheories takes a list of profiles and transforms into a map
   from theories to profiles where each profile is assigned to its theory.
-}
assignProfilesToTheories :: (Eq sid,Ord t,Ord fid,Ord p)
                            => [Profile t fid sid p]
                            -> M.Map t [Profile t fid sid p]
assignProfilesToTheories ps = foldr updateMap M.empty ps
    where updateMap p m = M.insertWith extendProfiles (theory p) [p] m
              where extendProfiles _ oldps = p:oldps

{- |
   profileMorphs1 takes a list of profiles from a source and a target theory 
   and returns a list of profile morphism such that for each morphism from this list
   and each profile from the source list there exists an equivalent profile
   in the target list modulo this profile morphism.
   Moreover the list of profile morphisms is complete.
   Note: All target profiles are assumed to be from the same theory!
   To garantee this profileMorphs1 is only used in 'profileMoprhs'.
-}
profileMorphs1 :: (Eq sid,Ord fid,Ord p)
                  => [Profile t fid sid p]   -- ^ the list of source profiles
                      -> [Profile t fid sid p]   -- ^ the list of target profiles
                      -> [ProfileMorphism fid p] -- ^ list of all morphisms from the source to the target
profileMorphs1 sourceProfiles targetProfiles =
    let sourcePms = map (buildListOfProfileMorphs targetProfiles) sourceProfiles
        cleanUp (fmap,pmap) = (M.filterWithKey (/=) fmap,M.filterWithKey (/=) pmap)        
    in case (if elem [] sourcePms -- if there is a source formula that can't be mapped to a target formula
             then Nothing -- then there can't be any profile morphism for all source formulas
             else Just sourcePms) -- Note: the incomplete profile morphism could be interesting for profile intersection
       of (Just pms) -> map cleanUp (foldl1 mergeListOfProfileMorphs pms)
          Nothing -> []

{- |
   buildListProfileMorphs takes a list of target profiles and a single source profile
   and returns the list of profile morphisms such that for each morphism from this list
   there exists a profile in the target list which is a translation of the source profile
   via this morphism. Moreover the list of profile morphisms is complete.
   This function is only used inside 'profileMorphisms'.
-}
buildListOfProfileMorphs :: (Eq sid,Ord p) => [Profile t fid sid p] -> Profile t fid sid p -> [ProfileMorphism fid p]
buildListOfProfileMorphs targetPms (Profile _ fidS sidS plS) = 
    [(M.singleton fidS fidT, makeParamMap plS plT) | 
     (Profile _ fidT sidT plT) <- targetPms, sidS == sidT, isRightUnique (zip plS plT)]
        where makeParamMap pl1 pl2 = M.fromList (zip pl1 pl2)

{- |
   mergeListOfProfileMorphs is a commutative function that merges two lists of profile morphism.
   The result is empty iff each pair of profile morphism (from the cartesian product of these two lists)
   can't be merged consistently (see 'mergeProfileMorphs').
-}
mergeListOfProfileMorphs :: (Ord fid,Ord p) => [ProfileMorphism fid p] -> [ProfileMorphism fid p] -> [ProfileMorphism fid p]
mergeListOfProfileMorphs spm1 spm2 = 
    [mergeProfileMorphs pm1 pm2 | pm1 <- spm1, pm2 <- spm2, consistentProfileMorphisms pm1 pm2]


{- |
   mergeProfileMorphs is a commutative function that merges two profile morphism.
-}
mergeProfileMorphs :: (Ord fid,Ord p) => ProfileMorphism fid p -> ProfileMorphism fid p -> ProfileMorphism fid p
mergeProfileMorphs (fid1,p1) (fid2,p2) = (M.union fid1 fid2,M.union p1 p2)


{- |
   two profile morphisms are consistent iff their parameter list are consistent
-}
consistentProfileMorphisms :: (Ord p) => ProfileMorphism fid p -> ProfileMorphism fid p -> Bool
consistentProfileMorphisms (fid1,p1) (fid2,p2) = consistent p1 p2


{- |
   two maps are consistent iff they have the same values on their common support
   todo: the momentary implementation is very inefficeint.
-}
consistent :: (Ord a,Ord b) => M.Map a b -> M.Map a b -> Bool
consistent m1 m2 = (M.intersection m1 m2) == (M.intersection m2 m1)

{- |
   two profiles are said to be duplicates if they have the same skeletons and paramters.
-}
removeDuplicateProfiles :: (Eq sid,Ord t,Ord fid,Ord p) => [Profile t fid sid p] -> [Profile t fid sid p]
removeDuplicateProfiles profiles = nubBy eqProfiles profiles
    where eqProfiles p1 p2 = (skeleton p1) == (skeleton p2) &&
                             (parameter p1) == (parameter p2)

{-
------ test data
*Common.Matching> assignProfilesToTheories [Profile "t1" 1 1 [],Profile "t2" 2 2 [],Profile "t1" 2 2 []]
fromList [("t1",[Profile {theory = "t1", formulaId = 1, skeleton = 1, parameter = []},Profile {theory = "t1", formulaId = 2, skeleton = 2, parameter = []}]),("t2",[Profile {theory = "t2", formulaId = 2, skeleton = 2, parameter = []}])]

-- source

sourceProfiles = [nfa1,nfb1]

nfa1 = Profile 'a' [1,2,3] "nfa1"

nfb1 = Profile 'b' [1,2] "nfb1"

-- target

targetProfiles = [nfa2,nfa3,nfb2]

nfa2 = Profile 'a' [4,4,5] "nfa2"

nfa3 = Profile 'a' [6,7,8] "nfa3"

nfb2 = Profile 'b' [4,4] "nfb2"


*Common.Matching2> profileMorphisms sourceProfiles targetProfiles
[(fromList [("nfa1","nfa2"),("nfb1","nfb2")],fromList [(1,4),(2,4),(3,5)])]

*Common.Matching2> buildListOfProfileMorphs targetProfiles nfa1
[(fromList [("nfa1","nfa2")],fromList [(1,4),(2,4),(3,5)]),(fromList [("nfa1","nfa3")],fromList [(1,6),(2,7),(3,8)])]
-}