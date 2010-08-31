{- |
Module      :  $Header$
Description :  Logic independent retrieval functionality
Copyright   :  (c) Immanuel Normann, Uni Bremen 2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  inormann@jacobs-university.de
Stability   :  provisional
Portability :  portable
-}

module Search.Common.Select where

import Search.Common.Data hiding (parameter,role)
import Data.List as L
import Data.Set as S
import Data.Map as M hiding ((!))
import Data.Maybe (catMaybes)
import Search.Utils.SetMap as SM --(fromListSetValues)
import Search.Utils.List
import Database.HaskellDB
import Database.HaskellDB.DriverAPI
import Database.HaskellDB.HDBRec
import Search.DB.Connection
import Search.DB.FormulaDB.Profile



-- -----------------------------------------------------------
-- *  Principle Functions
-- -----------------------------------------------------------

{- |
   search is the main function of this module. It takes a handler function
   to read in the source theory and a path to the file of the source theory
   and returns all possible profile morphisms from all matching target theories
   in the database.
-}
search :: (Ord p, Read p, Show p) =>
          (FilePath -> TheoryName -> IO ([ShortProfile p], [ShortProfile p]))
       -> FilePath
       -> TheoryName
       -> IO [[LongInclusionTuple p]]
search getSourceProfiles dir file =
    let skelOf (skel,_,_,_) = skel
    in do (axioms,theorems) <- getSourceProfiles dir file
          axioms' <- return $ removeDuplicateProfiles axioms
          targetCandidates <- allTargetCandidates (L.map skelOf axioms')
          mapM (showResults file axioms' theorems) (M.toList targetCandidates)

{- |
   showResults shows for a given target theory candidate all possible profile morphisms
   and the actual reused theorems.
-}
showResults :: (Ord p, Read p, Show p) =>
               TheoryName
               -> [ShortProfile p]
               -> [ShortProfile p]
               -> (String, Map Skel (Set ([p], LineNr)))
               -> IO [LongInclusionTuple p]
showResults sourceTheory sAxioms sTheorems (targetTheory,tMap) =
    let sAxioms' = (L.map toProfile2 sAxioms)
        morphs = profileMorphism sAxioms' tMap
        toProfile2 (skel, ps, lineNr, _) = (skel, (ps, lineNr))
        toIncTuple (st,tt,ps,lm,lines) =  (st,tt,ps,lm,length lines)
    in do putStrLn targetTheory
          targetProfiles <- getProfilesFromDB targetTheory
          longIncTuples <- return (L.map (inclusionTuple sourceTheory targetTheory
                                                   targetProfiles sTheorems)
                                   morphs)
          multiInsertInclusion (L.map toIncTuple longIncTuples)
          return longIncTuples


inclusionTuple :: (Eq p,Ord p) =>
                  TheoryName  -- ^ source theory
               -> TheoryName  -- ^ target theory
               -> [ShortProfile p] -- ^ profiles of target sentences
               -> [ShortProfile p] -- ^ profiles of source theorems
               -> (Renaming p, LineMap) -- ^ profile mapping
               -> LongInclusionTuple p -- ^ profiles of reused source theorems
inclusionTuple st tt ts ss (ren,lmap) = (st,tt,ren',lmap',newTheorems)
    where newTheorems = L.map lineOf $ reusedTheorems ts ss ren
          lineOf (_,_,lNr,_) = lNr
          neq a b = a /=b
          ren' = M.filterWithKey neq ren
          lmap' = M.filterWithKey neq lmap

reusedTheorems :: (Eq p,Ord p) => [ShortProfile p] -> [ShortProfile p] -> Renaming p -> [ShortProfile p]
reusedTheorems tSens sTheorems renaming = L.filter reusedTheorem sTheorems'
    where sTheorems' = L.map (translate renaming) sTheorems
          neq (s1,p1,_,_) (s2,p2,_,_) = (s1 /= s2) || (p1 /= p2)
          reusedTheorem s = all (neq s) tSens

translate :: (Ord p) => Renaming p -> ShortProfile p -> ShortProfile p 
translate renaming (skel,param,lnr,role) = (skel,param',lnr,role)
    where param' = L.map (f renaming) param
          f renaming param = findWithDefault param param renaming

getProfilesFromDB :: (Read p) => TheoryName -> IO [ShortProfile p]
getProfilesFromDB targetTheory =
    let q = do t <- table profile  -- the query
	       restrict ((t!file) .==. (constant targetTheory))
	       project (skeleton_md5 << t!skeleton_md5 # 
                        parameter << t!parameter # 
                        line << t!line # role << t!role)
        recToTuple rec = (skel, (read parameter) , line, role)
            where (RecCons skel (RecCons parameter (RecCons line (RecCons role _)))) = 
                      rec RecNil
    in do recs <- myQuery q
          return $ L.map recToTuple recs

{- |
   two profiles are said to be duplicates if they have the same skeletons and parameters.
-}
removeDuplicateProfiles :: (Eq p) => [ShortProfile p] -> [ShortProfile p]
removeDuplicateProfiles profiles = nubBy eqProfiles profiles
    where eqProfiles (skel1,par1,_,_) (skel2,par2,_,_) = 
              skel1 == skel2 && par1 == par2

-- -----------------------------------------------------------
-- *  Database Access
-- -----------------------------------------------------------


{- |
   allTargetCandidates takes a list of skeletons and retrieves from the database
   candidates of target theories. A theory is a candidate if it contains all the
   skeletons from the input list.
-}
allTargetCandidates :: (Ord p, Read p) => 
                       [Skel] -> IO (Map TheoryName (Map Skel (Set ([p], LineNr))))
allTargetCandidates skels =
    let len = length $ nub skels
        comprisesAllSkels skelLineSet = 
                     ((S.size $ S.map fst skelLineSet) == len)
    in do triples <- matchSkeleton skels
          return $ (M.map fromSetSetValues
                         (M.filter comprisesAllSkels (fromListSetValues triples)))

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


-- -----------------------------------------------------------
-- *  Matching
-- -----------------------------------------------------------


{- |
   profileMorphism finds all theory morphisms from profiles of a source theory
   to profiles in a target theory.
-}
profileMorphism :: (Ord p, Read p) =>
                   [(Skel,([p], LineNr))] -- ^ source profiles
                       -> M.Map Skel (S.Set ([p], LineNr)) -- ^ map from skeletons to target profile
                       -> [(Renaming p, LineMap)]
profileMorphism sourceProfiles targetProfileMap =
    let  matchList' (s,sourceProfile) = 
             case M.lookup s targetProfileMap
             of (Just targetProfiles) -> matchList (S.toList targetProfiles) sourceProfile
                Nothing -> []
    in case (L.map matchList' sourceProfiles)
       of (h:t) -> foldr merge h t
          [] -> []

{- |
   merge takes two lists of profile mappings and returns the list of
   all profile mappings resulting from a admissible union out of the
   Cartesian product of the input lists. A union is of two profile mappings
   is admissible iff their renamings are equal on their common domain.
-}
merge :: (Ord p, Read p) => [(Renaming p, LineMap)]
                 -> [(Renaming p, LineMap)]
                 -> [(Renaming p, LineMap)]
merge ps1 ps2 = catMaybes [merge' p1 p2 | p1 <- ps1, p2 <- ps2]
    where merge' (r1,l1) (r2,l2) =
              case maybeUnion r1 r2
              of (Just r) -> Just (r, M.union l1 l2)
                 Nothing -> Nothing

{- |
   matchList takes  a list of target pairs and a single source pair
   and returns a list of renamings together with a line number mapping.
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
   and a line number as second. Each pair represents a formula
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

