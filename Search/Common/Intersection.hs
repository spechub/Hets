{- |
Module      :  $Header$
Description :  Theory intersection
Copyright   :  (c) Immanuel Normann, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  inormann@jacobs-university.de
Stability   :  provisional
Portability :  portable
-}
module Search.Common.Intersection where

--import Search.Common.Matching 
import Search.Utils.List (allJust,isRightUnique)
import Data.List hiding (union)
import Data.Map (Map,fromList,union,intersection)
--import Data.Set hiding (map)


data Profile t fid sid p =
    Profile 
    { theory :: t,       -- ^ 't' is the theory where the profile belongs to
      formulaId :: fid,  -- ^ 'fid' is the id of the original formula relative to the theory 't'
      skeleton :: sid, -- ^ 'sid' the skeleton (or an representative id); i.e. the abstracted formula resulting from normalization
      parameter :: [p]   -- ^ '[p]' are the corresponding formula parameter
    } deriving (Eq, Ord, Show)

type ProfileMorphism s p = (FormulaIdMap s,ParameterMap p)
type FormulaIdMap fid = Map fid fid -- from source to target
type ParameterMap p = Map p p -- from source to target


--type Incompatibles a p s = (Set (ProfilePair a p s), (ProfilePair a p s))
type ProfilePair a p s = (a,(s,s),ParameterMap p)
{-
evalIncMatrix :: Set (Incompatibles a p s) -> Set (ProfilePair a p s)
evalIncMatrix m =
    if empty m
    then m
    else insert c (evalIncMatrix m')
        where (pps,pp) = findMin m
              m' = del pps 
-}
--------------------------------
intersectProfiles :: (Eq t,Ord s,Ord p,Ord f) => [Profile t f s p] -> [Profile t f s p] -> [ProfileMorphism f p]
intersectProfiles ps1 ps2 = map profileMorph compatibleProfilePairs
    where profilePairs = allJust $ concatMap (\p -> map (profilePair p) ps2) ps1
          compatibleProfilePairs = updateProfileMatrix [[]] profilePairs -- oder '[]' statt '[[]]'???
          --getAbs (a,_,_) = a
          getSs (_,(s1,s2),_) = (s1,s2)
          getPm (_,_,pm) = pm
          profileMorph ppRow = ((fromList $ map getSs ppRow),(foldl1 union (map getPm ppRow)))

profilePair :: (Eq t, Eq s, Ord p) => Profile t f s p -> Profile t f s p -> Maybe (ProfilePair s p f)
profilePair (Profile t1 f1 s1 p1) (Profile t2 f2 s2 p2) =
    let paraAssoc = (zip p1 p2)
--    in if (t1,s1) == (t2,s2) -- skeletons and theory must be identical -- warum theory ???
    in if s1 == s2 -- skeletons must be identical
           && isRightUnique paraAssoc
       then Just (s1, (f1,f2), fromList paraAssoc)
       else Nothing

sortProfileMatrix :: (Ord a) => [[ProfilePair a p s]] -> [[ProfilePair a p s]]
sortProfileMatrix ppMatrix = sortBy comp ppMatrix
    where comp ppRow1 ppRow2 =
              case compare (numOfAbs ppRow1) (numOfAbs ppRow2) -- the more different abstractions the higher the quality
              of EQ -> compare (length ppRow1) (length ppRow2)
                 ltOrgt -> ltOrgt
          numOfAbs pps = nub (map getAbs pps)
          getAbs (a,_,_) = a

updateProfileMatrix :: (Ord a,Ord p) => [[ProfilePair a p s]] -> [ProfilePair a p s] -> [[ProfilePair a p s]]
updateProfileMatrix ppMatrix [] = sortProfileMatrix (map reverse ppMatrix)
updateProfileMatrix ppMatrix (pp:pps) =
    let (compatibles,incompatibles) = partition (isCompatibleWith pp) ppMatrix
    in case compatibles
       of [] -> updateProfileMatrix (updateMax incompatibles pp) pps
          _ -> updateProfileMatrix ((map (pp:) compatibles) ++ incompatibles) pps

updateMax :: (Ord p) => [[ProfilePair a p s]] -> ProfilePair a p s -> [[ProfilePair a p s]]
updateMax ppMatrix pp = updatedRow:ppMatrix
    where comp pp ppRow1 ppRow2 = compare (numOfCompatibles pp ppRow1) (numOfCompatibles pp ppRow2)
          maximalCompatibleRow = maximumBy (comp pp) ppMatrix
          updatedRow = pp:(filter (consistentProfilePair pp) maximalCompatibleRow)

isCompatibleWith :: (Ord p) => ProfilePair a p s -> [ProfilePair a p s] -> Bool
isCompatibleWith pp pps = all (consistentProfilePair pp) pps

consistentProfilePair:: (Ord p) => ProfilePair a p s -> ProfilePair a p s -> Bool
consistentProfilePair (_,_,p1) (_,_,p2) = consistent p1 p2

numOfCompatibles :: (Ord p) => ProfilePair a p s -> [ProfilePair a p s] -> Int
numOfCompatibles pp pps = length (map (consistentProfilePair pp) pps)

{-
Test Data
 -}

{- |
   two maps are consistent iff they have the same values on their common support
   todo: the momentary implementation is very inefficeint.
-}
consistent :: (Ord a,Ord b) => Map a b -> Map a b -> Bool
consistent m1 m2 = (intersection m1 m2) == (intersection m2 m1)

-- Profiles

abelian_ring = [comAR1, comAR2, assAR1, assAR2, distAR, invAR, neutAR]

comAR1 = Profile "abelian_ring" 1 "com" ["times"]
comAR2 = Profile "abelian_ring" 2 "com" ["plus"]
assAR1 = Profile "abelian_ring" 3 "ass" ["times"]
assAR2 = Profile "abelian_ring" 4 "ass" ["plus"]
distAR = Profile "abelian_ring" 5 "dist" ["times","plus"]
invAR = Profile "abelian_ring" 6 "inv" ["plus","minus"]
neutAR = Profile "abelian_ring" 7 "neut" ["plus","zero"]

ring_with_one = [comRO, assRO1, assRO2, distRO, invRO, neutRO1, neutRO2]

comRO = Profile "ring_with_one" 1 "com" ["add"]
assRO1 = Profile "ring_with_one" 2 "ass" ["mult"]
assRO2 = Profile "ring_with_one" 3 "ass" ["add"]
distRO = Profile "ring_with_one" 4 "dist" ["mult","add"]
invRO = Profile "ring_with_one" 5 "inv" ["add","sub"]
neutRO1 = Profile "ring_with_one" 6 "neut" ["add","null"]
neutRO2 = Profile "ring_with_one" 7 "neut" ["mult","one"]



-- ProfilePairs

com12 = ("com",(1,2),fromList [(1,6)])
com31 = ("com",(3,1),fromList [(2,6)])
ass21 = ("ass",(2,1),fromList [(1,5)])
ass23 = ("ass",(2,3),fromList [(1,6)])
ass41 = ("ass",(4,1),fromList [(2,5)])
ass43 = ("ass",(4,3),fromList [(2,6)])
dist = ("dist",(5,4),fromList [(1,5),(2,6)])
inv = ("inv",(6,5),fromList [(2,6),(3,7)])
neut76 = ("neut",(7,6),fromList [(2,6),(4,8)])
neut77 = ("neut",(7,7),fromList [(2,5),(4,9)])

{-
*Utils.Intersection> updateProfileMatrix [[]] [com12,com31,ass21,ass23,ass41,ass43,dist,inv,neut76,neut77]
[[("com",(1,2),fromList [(1,6)]),("ass",(2,3),fromList [(1,6)]),("ass",(4,1),fromList [(2,5)]),("neut",(7,7),fromList [(2,5),(4,9)])],
[("com",(3,1),fromList [(2,6)]),("ass",(2,1),fromList [(1,5)]),("ass",(4,3),fromList [(2,6)]),("dist",(5,4),fromList [(1,5),(2,6)]),("inv",(6,5),fromList [(2,6),(3,7)]),("neut",(7,6),fromList [(2,6),(4,8)])],
[("com",(1,2),fromList [(1,6)]),("com",(3,1),fromList [(2,6)]),("ass",(2,3),fromList [(1,6)]),("ass",(4,3),fromList [(2,6)]),("inv",(6,5),fromList [(2,6),(3,7)]),("neut",(7,6),fromList [(2,6),(4,8)])]]

*Common.Intersection> intersectProfiles ring_with_one abelian_ring
[(fromList [(1,1),(2,3),(3,3)],fromList [("add","times"),("mult","times")]),
 (fromList [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7)],fromList [("add","plus"),("mult","times"),("null","zero"),("sub","minus")]),(fromList [(1,1),(2,4),(3,3),(7,7)],fromList [("add","times"),("mult","plus"),("one","zero")])]


-}