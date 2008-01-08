{- |
Module      :  $Header$
Description :  layout of the theory database
Copyright   :  (c) Immanuel Normann, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  inormann@jacobs-university.de
Stability   :  provisional
Portability :  portable
-}

{-
mysql> describe profile;
+------------------+----------------------------+------+-----+---------+-------+
| Field            | Type                       | Null | Key | Default | Extra |
+------------------+----------------------------+------+-----+---------+-------+
| library          | char(32)                   | YES  |     | NULL    |       | 
| file             | char(255)                  | YES  |     | NULL    |       | 
| line             | int(11)                    | YES  |     | NULL    |       | 
| formula          | text                       | YES  |     | NULL    |       | 
| skeleton         | text                       | YES  |     | NULL    |       | 
| skeleton_md5     | char(32)                   | YES  |     | NULL    |       | 
| parameter        | text                       | YES  |     | NULL    |       | 
| role             | enum('axiom','conjecture') | YES  |     | NULL    |       | 
| norm_strength    | enum('strong','weak')      | YES  |     | NULL    |       | 
| skeleton_length  | int(11)                    | YES  |     | NULL    |       | 
+------------------+----------------------------+------+-----+---------+-------+

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
module Search.DBSpec where
 
import Config (hsSource)
import Database.HaskellDB
import Database.HaskellDB.DBSpec
import Database.HaskellDB.FieldType
import Database.HaskellDB.DBSpec.DBSpecToDBDirect

{-
 executing createDBInfo creates haskell source files at .../Matching/DB
 which implement the connections to the database.
 Repelace afterwards "module XY" by "module DB.XY" with
 cd ./DB
 sed -i 's/module /module DB./' MPTP.hs MPTP/*
-}
createDBInfo = dbInfoToModuleFiles (hsSource ++ "/Matching/DB") "MPTP" dbInfo

dbInfo = DBInfo {
                 dbname = "mptp",
                 opts = DBOptions {useBString = False},
                 tbls = [profile,statistics,inclusion]
                }

{- profile -}
 
profile = makeTInfo "profile" [library, file, line, formula, skeleton, skeleton_md5,
                               parameter, role, norm_strength, skeleton_length]

library = makeCInfo "library" (StringT,False)
file = makeCInfo "file" (StringT,False)
line = makeCInfo "line" (IntT,False)
formula = makeCInfo "formula" (StringT,False)
skeleton = makeCInfo "skeleton" (StringT,False)
skeleton_md5 = makeCInfo "skeleton_md5" (StringT,False)
parameter = makeCInfo "parameter" (StringT,False)
role = makeCInfo "role" (StringT,False)
norm_strength = makeCInfo "norm_strength" (StringT,False)
skeleton_length = makeCInfo "skeleton_length" (IntT,False)

{- statistics -}

statistics = makeTInfo "statistics" [library, file, tautologies, duplicates, formulae]

tautologies = makeCInfo "tautologies" (IntT,False)
duplicates = makeCInfo "duplicates" (IntT,False)
formulae = makeCInfo "formulae" (IntT,False)

{- inclusion -}

inclusion = makeTInfo "inclusion" [source, target, line_assoc, morphism, morphism_size]

source = makeCInfo "source"  (StringT,False)
target = makeCInfo "target"  (StringT,False)
line_assoc = makeCInfo "line_assoc"  (StringT,False)
morphism = makeCInfo "morphism"  (StringT,False)
morphism_size = makeCInfo "morphism_size"  (IntT,False)