{- |
Module      :  $Header$
Description :  General connection to the database
Copyright   :  (c) Immanuel Normann, Uni Bremen 2007
License     :  GPLv2 or higher

Maintainer  :  inormann@jacobs-university.de
Stability   :  provisional
Portability :  portable
-}
module Search.DB.Connection where

import Database.HaskellDB.HSQL.MySQL

import Data.Map (Map)
import Database.HaskellDB
import Database.HaskellDB.Database
--import Database.HaskellDB.DriverAPI
import Database.HaskellDB.HDBRec
import Search.DB.FormulaDB.Profile as P
import Search.DB.FormulaDB.Inclusion as I
import Search.DB.FormulaDB.Statistics as S

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

--   ProfileTuple = (library',file',line',role',formula',skeleton',parameter',norm_strength')
type ProfileTuple = (String, String, Int, String, String, String, String, String, String, Int)
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


multiInsertProfiles :: (Show a, Show t1, Show t) =>
                       [(String, String, Int, String, t, a, t1, String)] -> IO ()
multiInsertProfiles recs = myMultiInsert profile (map profile2clause recs)


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

type FormulaIdMap fid = Map fid fid -- from source to target
type ParameterMap p = Map p p -- from source to target
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


insertInclusion rec = myInsert inclusion (inclusion2clause rec)

multiInsertInclusion :: (Show f, Show p) => [InclusionTuple f p] -> IO ()
multiInsertInclusion recs = myMultiInsert inclusion (map inclusion2clause recs)


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
type StatisticsRec =    
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

stat2clause :: StatisticsTuple -> StatisticsRec
stat2clause (library',file',nrOfTautologies,nrOfDuplicates,len) =
    ((S.library << constant library') #
     (S.file << constant file') #
     (tautologies << constant nrOfTautologies) #
     (duplicates << constant nrOfDuplicates) #
     (formulae << constant len)) -- the number of formulae without tautologies and duplicates

insertStatistics :: StatisticsTuple -> IO ()
insertStatistics stat = myInsert statistics (stat2clause stat)

{- 
 DATABASE CONNECTION
connect :: (MonadIO m) => DriverInterface -> [(String, String)] -> (Database -> m a) -> m a
-}
--options = [("server","localhost"),("db","formulaDB"),("uid","constructive"),("pwd","constructive")]
options = [("server","localhost"),("db","formulaDB"),("uid","active"),("pwd","pi=3,141")]

myConnect :: (Database -> IO a) -> IO a
myConnect = connect driver options
--myConnect = connect defaultdriver [] -- todo: set real driver and options
--see: Search.Config (home,dbDriver,dbServer,dbDatabase,dbPassword,dbUsername)

myQuery :: (GetRec er vr) => Query (Rel er) -> IO [Record vr]
myQuery q = myConnect (\db -> query db q)

myInsert table rec = do myConnect (\db -> insert db table rec)

myMultiInsert table recs = do myConnect (\db -> mapM_ (insert db table) recs)