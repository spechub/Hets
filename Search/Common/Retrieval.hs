{- |
Module      :  $Header$
Description :  Logic independent retrieval functionality
Copyright   :  (c) Immanuel Normann, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  inormann@jacobs-university.de
Stability   :  provisional
Portability :  portable
-}

module Search.Common.Retrieval where

import Config (dbDriver,dbServer,dbDatabase,dbPassword,dbUsername)
import Data.List (sortBy)
import Search.Common.Normalization -- ?
import Database.HaskellDB
import Database.HaskellDB.GenericConnect
import Database.HaskellDB.HDBRec
import DB.Connection
import DB.MPTP.Profile hiding (Skeleton)
import Search.Common.Matching hiding (parameter)
import qualified Data.List as L
import qualified Data.Set as S
import qualified Data.Map as M
import MD5

-- * Retrieval 

type FormulaId = Int

recordMorphisms :: (Read p,Show c, Show p, Ord p, Eq c) =>
                   FilePath
                       -> IO [Profile Theory Int (Skeleton c) [p]]
                       -> IO (M.Map Theory [ProfileMorphism Int [p]])
recordMorphisms source getProfiles =
    do morphs <- retrieveMorphisms getProfiles
       multiInsertInclusion $ insertMorphisms source morphs
       return morphs

insertMorphisms :: (Ord p) => FilePath -> M.Map Theory [ProfileMorphism f [p]] -> [InclusionTuple f [p]]
insertMorphisms source tpms = concatMap mkRec (M.toList tpms)
    where mkRec (target,((fm,pm):fpms)) = (source, target, fm, pm, M.size pm):(mkRec (target,fpms))
          mkRec (_,[]) = []

{- |
  
-}
retrieveMorphisms :: (Read p,Show c,Ord p,Eq c) 
                     => IO [Profile Theory Int (Skeleton c) [p]]
                         -> IO (M.Map Theory [ProfileMorphism Int [p]]) 
retrieveMorphisms getProfiles = 
    do (_,sps,tps) <- retrieveSource getProfiles
       return (profileMorphs sps tps)


retrieveSource getProfiles =
    do profiles <- getProfiles
       let nonTrivialProfiles = sortProfiles $ removeDuplicateProfiles $ 
                                removeTrueAtoms profiles -- todo: delete conjecture!!!
	   (md5s,sourceProfiles) = toMd5sAndProfiles nonTrivialProfiles
	   in do targetProfiles <- retrieveProfiles md5s
		 return (nonTrivialProfiles,sourceProfiles,targetProfiles)

retrieveProfiles (md5nf:md5nfs) =
    do recs <- retrieveMd5 [] md5nf
       profiles <- return (map (recToProfile 1) recs)
       retrieveNext 2 (map theory profiles) [profiles] md5nfs

retrieveNext :: (Read p,Num sid) => sid
                    -> [String]
                    -> [[Profile String Int sid [p]]]
                    -> [String]
                    -> IO [Profile String Int sid [p]]
retrieveNext nr [] _ _ =  return []
retrieveNext nr files accProfiles [] = return (filterProfiles files (concat accProfiles))
retrieveNext nr files accProfiles (md5nf:md5nfs) =
    do recs <- retrieveMd5 files md5nf
       profiles <- return (map (recToProfile nr) recs)
       retrieveNext (nr+1) (getCommonFiles files profiles) (profiles:accProfiles) md5nfs

retrieveMd5 files md5nf =
    do withDB $ do t <- table profile
		   restrict (allConstraints t md5nf files) -- .&&. (t!file .==. (constant "connsp_3__t24_connsp_3.dfg")))
		   project (file << t!file #
			    line << t!line #
			    parameter << t!parameter)

-- todo: das lokal in retrieveMd5 verstecken
allConstraints t nf [] = (t!skeleton_md5 .==. (constant nf))
allConstraints t nf fs = (t!skeleton_md5 .==. (constant nf)) .&&. (fileConstraint t fs)
fileConstraint t [f] = (t!file .==. constant f) -- .&&. (t!file .==. (constant "connsp_3__t24_connsp_3.dfg"))
fileConstraint t (f:fs) = (t!file .==. constant f) .||. (fileConstraint t fs)


-- * Helper Functions



-- ** Data Structure Translator
{- |
  
-}
toMd5sAndProfiles :: (Num sid,Show c) => [Profile t f (Skeleton c) [p]] -> ([String],[Profile t f sid [p]])
toMd5sAndProfiles nfProfiles = (md5Strings,nrProfiles)
    where nfProfileAssoc _ [] = []
	  nfProfileAssoc nr (nfp:nfps) = (nfToMd5 nr nfp):(nfProfileAssoc (nr+1) nfps)
	  nfToMd5 nr (Profile t f s ps) = (md5s $ Str $ show s,(Profile t f nr ps))
	  (md5Strings,nrProfiles) = unzip (nfProfileAssoc 1 nfProfiles)
          skel = Common.Matching.skeleton

--recToProfile :: (Read p) => sid -> ProfileRec -> Profile URI URI sid [p]
recToProfile :: (Read p) =>
                sid
                    -> (RecNil -> RecCons File t1 (RecCons Line t3 (RecCons Parameter String t5)))
                    -> Profile t1 t3 sid p
recToProfile nr rec = Profile file line nr params
    where (RecCons file (RecCons line (RecCons paramStr _))) = rec RecNil
	  params = (read paramStr) -- ::[p]


-- ** Filter Functions
{- |
   
-}
removeTrueAtoms :: [Profile t f (Skeleton c) [p]] -> [Profile t f (Skeleton c) [p]]
removeTrueAtoms profiles = filter isNotTrueAtom profiles
    where isNotTrueAtom (Profile _ _ (Const TrueAtom []) _) = False
	  isNotTrueAtom _ = True

filterProfiles :: (Eq t) => [t] -> [Profile t fid sid p] -> [Profile t fid sid p]
filterProfiles files profiles = filter isFromCommonFiles profiles
    where isFromCommonFiles rec = elem (theory rec) files

getCommonFiles :: (Eq t) => [t] -> [Profile t fid sid p] -> [t]
getCommonFiles oldfiles profiles = L.intersect oldfiles newfiles
    where newfiles = map theory profiles

	  
{-
getFile profile = file
    where (file,_) = sourceRef profile
-}

-- ** Others
{- |
   
-}

sortProfiles :: [Profile t f (Skeleton c) [p]] -> [Profile t f (Skeleton c) [p]]
sortProfiles ps = sortBy compNumOsNodes ps
    where compNumOsNodes p1 p2 = compare (skeletonSize p2) (skeletonSize p1)
          skeletonSize = countNodes . (Common.Matching.skeleton)
