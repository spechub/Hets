{- |
Module      :  $Header$
Description :  General connection to the database
Copyright   :  (c) Immanuel Normann, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  inormann@jacobs-university.de
Stability   :  provisional
Portability :  portable
-}
module Search.DB.Connection where

import Config (home,dbDriver,dbServer,dbDatabase,dbPassword,dbUsername)
import Database.HaskellDB
import Database.HaskellDB.GenericConnect
import Database.HaskellDB.HDBRec
import Data.List (sort)
import Data.Map (size)
import Search.DB.MPTP.Profile as P
import Search.DB.MPTP.Inclusion as I
import Search.DB.MPTP.Statistics as S
import Search.Common.Matching hiding (skeleton,parameter)
import Search.Common.Normalization as N
import MD5


type URI = String
type Theory = URI
type SourceTheory = URI
type TargetTheory = URI


{- TODO:
   - handle success/failure info from the database
   - provide signatures and types
-}

{- PROFILE

mysql> describe profile;
+-----------------+----------------------------+------+-----+---------+-------+
| Field           | Type                       | Null | Key | Default | Extra |
+-----------------+----------------------------+------+-----+---------+-------+
| library         | char(32)                   | YES  |     | NULL    |       | 
| file            | char(255)                  | YES  |     | NULL    |       | 
| line            | int(11)                    | YES  |     | NULL    |       | 
| formula         | text                       | YES  |     | NULL    |       | 
| skeleton        | text                       | YES  |     | NULL    |       | 
| skeleton_md5    | char(32)                   | YES  |     | NULL    |       | 
| parameter       | text                       | YES  |     | NULL    |       | 
| role            | enum('axiom','conjecture') | YES  |     | NULL    |       | 
| norm_strength   | enum('strong','weak')      | YES  |     | NULL    |       | 
| skeleton_length | int(11)                    | YES  |     | NULL    |       | 
+-----------------+----------------------------+------+-----+---------+-------+
-}

-- todo: type ProfileTuple = (library',file',line',role',formula',skeleton',parameter',norm_strength')
type ProfileRec =
    RecNil -> 
        RecCons P.Library
           (Expr String)
	   (RecCons P.File
		    (Expr String)
		    (RecCons P.Line
			     (Expr Int)
			     (RecCons P.Formula
				      (Expr String)
				      (RecCons P.Skeleton
					       (Expr String)
					       (RecCons P.Skeleton_md5
							(Expr String)
							(RecCons P.Parameter
								 (Expr String)
								 (RecCons P.Role
									  (Expr String)
									  (RecCons P.Norm_strength
										   (Expr String)
										   (RecCons Skeleton_length
											    (Expr Int)
											    RecNil)))))))))


profile2clause (library',file',line',role',formula',skeleton',parameter',norm_strength') =
    ((P.library << constant library') #
     (P.file << constant file') #
     (line << constant line') #
     (formula << (constant $ md5s $ Str $ show formula')) #
     -- (formula << (constant $ show formula')) #
     (skeleton << (constant $ show skeleton')) #
     (skeleton_md5 << (constant $ md5s $ Str $ show $ skeleton')) #
     (parameter << constant (show parameter')) #
     (role << constant role') #
     (norm_strength << constant norm_strength') #
     (skeleton_length << (constant $ length $ show skeleton')))


insertProfile db req = insert db profile (profile2clause req)

multiInsertProfiles :: (Show a, Show t1, Show t) =>
                       [(String, String, Int, String, t, a, t1, String)] -> IO [()]
multiInsertProfiles reqs = do connect (\db -> mapM (insertProfile db) reqs)


{- INCLUSION

mysql> describe inclusion;
+---------------+-----------+------+-----+---------+-------+
| Field         | Type      | Null | Key | Default | Extra |
+---------------+-----------+------+-----+---------+-------+
| source        | char(255) | YES  |     | NULL    |       | 
| target        | char(255) | YES  |     | NULL    |       | 
| line_assoc    | text      | YES  |     | NULL    |       | 
| morphism      | text      | YES  |     | NULL    |       | 
| morphism_size | int(11)   | YES  |     | NULL    |       | 
+---------------+-----------+------+-----+---------+-------+

-}

type InclusionTuple f p = (URI, URI, FormulaIdMap f, ParameterMap p, Int)
type InclusionRec =
    RecNil -> 
        RecCons I.Source
	   (Expr String)
	   (RecCons I.Target
		    (Expr String)
		    (RecCons I.Line_assoc
			     (Expr String)
			     (RecCons I.Morphism
				      (Expr String)
				      (RecCons I.Morphism_size (Expr Int) RecNil))))




inclusion2clause :: (Show f, Show p) => InclusionTuple f p -> InclusionRec
inclusion2clause (source', target', line_assoc', morphism', morphism_size') =
    ((source <<- source') #
     (target <<- target') #
     (line_assoc <<- show line_assoc') #
     (morphism <<- show morphism') #
     (morphism_size <<- morphism_size'))

insertInclusion :: (Show f, Show p) => Database -> InclusionTuple f p -> IO ()
insertInclusion db req = insert db inclusion (inclusion2clause req)

multiInsertInclusion :: (Show f, Show p) => [InclusionTuple f p] -> IO [()]
multiInsertInclusion reqs = do connect (\db -> mapM (insertInclusion db) reqs)


{- STATISTICS

mysql> describe statistics;
+-------------+-----------+------+-----+---------+-------+
| Field       | Type      | Null | Key | Default | Extra |
+-------------+-----------+------+-----+---------+-------+
| library     | char(32)  | YES  |     | NULL    |       | 
| file        | char(255) | YES  |     | NULL    |       | 
| tautologies | int(11)   | YES  |     | NULL    |       | 
| duplicates  | int(11)   | YES  |     | NULL    |       | 
| formulae    | int(11)   | YES  |     | NULL    |       | 
+-------------+-----------+------+-----+---------+-------+

-}

type StatisticsTuple = (URI, Theory, Int, Int, Int)
type StatisticsReq =    
    RecNil ->
        RecCons S.Library
	   (Expr String)
	   (RecCons S.File
		    (Expr String)
		    (RecCons S.Tautologies
			     (Expr Int)
			     (RecCons S.Duplicates
				      (Expr Int)
				      (RecCons S.Formulae (Expr Int) RecNil))))


stat2clause :: StatisticsTuple -> StatisticsReq
stat2clause (library',file',nrOfTautologies,nrOfDuplicates,len) =
    ((S.library << constant library') #
     (S.file << constant file') #
     (tautologies << constant nrOfTautologies) #
     (duplicates << constant nrOfDuplicates) #
     (formulae << constant len)) -- the number of formulae without tautologies and duplicates

insertStatistics :: StatisticsTuple -> IO ()
insertStatistics stat = do connect (\db -> insert db statistics (stat2clause stat))



{- 
 DATABASE CONNECTION
-}

connect = genericConnect dbDriver [dbServer,dbDatabase,dbPassword,dbUsername]


{- aus haskelldb-0.9:
withDB q = genericConnect dbDriver [dbServer,dbDatabase,dbPassword,dbUsername] (performQuery q)

performQuery q db =
   do --putStrLn "Query:"
      --print q
      result <- query db q
      --putStrLn "Results:"
      --mapM_ print result
      --putStrLn (fileName result)
      return result
-}


{- todo: brauch ich das noch?
getField field =
    let unwrapRec rec = field
            where (RecCons field _) = rec RecNil
        select =
            do withDB $ do t <- table profile
		           project (field << t!field)
    in do recs <- select
          return $ sort (map unwrapRec recs)
-}
{- todo: withDB, performQuery is depracted and only used in Common/Rtrieval.hs
   should be replaced by appropriately
-}



{-
type FormulaId = Int

recToProfile :: (Read p) =>
                FormulaId
                    -> (RecNil -> RecCons P.File t1 (RecCons P.Line t3 (RecCons P.Parameter String t5)))
                    -> Profile t1 t3 FormulaId p
recToProfile nr rec = Profile file line nr params
    where (RecCons file (RecCons line (RecCons paramStr _))) = rec RecNil
	  params = (read paramStr) -- ::[p]
type TmpRec =
    RecNil -> (RecCons P.File
	       (Expr String)
	       (RecCons P.Line
		(Expr Int)
		(RecCons P.Parameter
		 (Expr String) RecNil)))
-}