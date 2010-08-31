{- |
Module      :  $EmptyHeader$
Description :  <optional short description entry>
Copyright   :  (c) <Authors or Affiliations>
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  <email>
Stability   :  unstable | experimental | provisional | stable | frozen
Portability :  portable | non-portable (<reason>)

<optional description>
-}
module Main where

import Search.Common.Data as D hiding (parameter,role)
import Data.List as L
import Data.Map as M hiding ((!))
import Database.HaskellDB
import Database.HaskellDB.DriverAPI
import Database.HaskellDB.HDBRec
import Search.DB.Connection
--import Search.DB.FormulaDB.Profile as P
import Search.DB.FormulaDB.Short_profile as SP
import SoftFOL.Sign --(SPTerm,)
--import Search.DB.FormulaDB.Skel_to_theory as ST
import Search.DB.FormulaDB.Theory as T
import Search.DB.FormulaDB.Inclusion as I
import Search.DB.FormulaDB.Sentence
import MD5
import System.Environment (getArgs)

main = do args <- getArgs
          case args of
            (source:target:renaming':_) -> 
                let renaming = (read renaming')::D.Renaming SPIdentifier 
                in do result <- newTheorem (source,target,renaming)
                      appendFile "/home/immanuel/dfg/log/reused-theorems" $ show $ result
            _ -> error "invalid arguments! It should be one of:\n???"

-- -----------------------------------------------------------
-- *  Theorem Reuse
-- -----------------------------------------------------------

{-
UPDATE [LOW_PRIORITY] [IGNORE] tbl_name
    SET col_name1=expr1 [, col_name2=expr2 ...]
    [WHERE where_condition]
    [ORDER BY ...]
    [LIMIT row_count]
-}

recordTheoremReuse :: (Bool,Bool) -> IO ()
recordTheoremReuse (absolute,relative) = undefined

newTheorems :: IO [Int] -- [(Bool, Bool)]
newTheorems = 
    do recs <- allInclusions -- [(source,target,renaming)]
       mapM newTheorem recs

newTheorem :: (TheoryName, TheoryName, D.Renaming SPIdentifier)
              -> IO Int -- (Bool, Bool)
newTheorem (sourceTheory,targetTheory,renaming) = -- theory is intended to be a source theory
    let toMd5 (skel,param) =  md5s $ Str (skel ++ (show $ apply renaming param))
    in do sourceTheoryId <- nameToTid sourceTheory
          targetTheoryId <- nameToTid targetTheory
          (skel,param) <- getTheoremOfTheory sourceTheoryId
          absolute <- absoluteNewTheorem (skel,apply renaming param) -- sourceTheoremMd5
          relative <- relativeNewTheorem (skel,param) targetTheoryId
          case (sourceTheory == targetTheory, relative, absolute)
            of (True,True,True) -> return 1
               (True,True,False) -> return 2
               (True,False,True) -> return 3 -- should not happen
               (True,False,False) -> return 4
               (False,True,True) -> return 5
               (False,True,False) -> return 6
               (False,False,True) -> return 7 -- should not happen
               (False,False,False) -> return 8
{-
          if absolute
            then return 2
            else do relative <- relativeNewTheorem (skel,param) targetTheoryId
                    if relative then return 1 else return 0
-}

relativeNewTheorem :: (TheoryName,[SPIdentifier]) -> Int -> IO Bool
relativeNewTheorem (sourceSkel,sourceParam) targetId =
    let q = do t <- table short_profile  -- the query
	       restrict ((t!SP.theory_id) .==. (constant targetId) .&&.
                         (t!SP.skeleton_md5) .==. (constant sourceSkel))
               project (SP.parameter << t!SP.parameter)
        recToTuple rec = parameter
            where (RecCons parameter _) = rec RecNil
    in do recs <- myQuery q -- assumming each theory in SoftFOL-MML as exactly one theorem
          return $ not $ L.elem (show sourceParam) $ L.map recToTuple recs

absoluteNewTheorem :: (TheoryName,[SPIdentifier]) -> IO Bool
absoluteNewTheorem (skel,param) = -- representing the source theorem
    let sourceTheoremMd5 = md5s $ Str (skel ++ (show $ param))
        q = do t <- table sentence
               restrict ((t!skel_param_md5) .==. (constant sourceTheoremMd5))
               project (skel_param_md5 << t!skel_param_md5)
    in do recs <- myQuery q -- tid <-> name is bijective mapping
          return $ (recs == [])

apply :: D.Renaming SPIdentifier -> [SPIdentifier] -> [SPIdentifier]
apply renaming param = param'
    where param' = L.map (f renaming) param
          f renaming param = findWithDefault param param renaming

allInclusions :: IO [(TheoryName,TheoryName,D.Renaming SPIdentifier)]
allInclusions =
    let q = do t <- table inclusion
               project (I.source << t!I.source #
                        I.target << t!I.target #
                        I.renaming << t!I.renaming)
        recToTuple rec = (source,target,read renaming)
            where (RecCons source (RecCons target (RecCons renaming _))) = rec RecNil
    in do recs <- myQuery q -- tid <-> name is bijective mapping
          return $ L.map recToTuple recs


getTheoremOfTheory :: TheoryId -> IO (Skel,[SPIdentifier])
getTheoremOfTheory theoryId = 
    let q = do t <- table short_profile  -- the query
	       restrict ((t!SP.theory_id) .==. (constant theoryId) .&&.
                         (t!SP.role) .==. (constant "conjecture"))
               project (SP.skeleton_md5 << t!SP.skeleton_md5 # 
                        SP.parameter << t!SP.parameter)
        recToTuple rec = (skel, read parameter)
            where (RecCons skel (RecCons parameter _)) = rec RecNil
    in do (rec:_) <- myQuery q -- assumming each theory in SoftFOL-MML as exactly one theorem
          return $ recToTuple rec

nameToTid :: TheoryName -> IO TheoryId
nameToTid name =
    let q = do t <- table theory
               restrict ((t!T.name) .==. (constant name))
               project (T.tid << t!T.tid)
        recToTuple rec = tid
            where (RecCons tid _) = rec RecNil
    in do (rec:_) <- myQuery q -- tid <-> name is bijective mapping
          return $ recToTuple rec

-- -----------------------------------------------------------
-- *  Database Access
-- -----------------------------------------------------------

type TheoryId = Int

getProfilesDFGFromDB n ss = (getProfilesFromDB n ss)::IO [ShortProfile String]

getProfilesFromDB :: (Read p) => TheoryId -> [Skel] -> IO [ShortProfile p]
getProfilesFromDB tTheoryId skels =
    let q = do t <- table short_profile  -- the query
	       restrict ((t!SP.theory_id) .==. (constant tTheoryId) .&&.
                         (_in (t!SP.skeleton_md5) (L.map constant skels)))
	       project (SP.skeleton_md5 << t!SP.skeleton_md5 # 
                        SP.parameter << t!SP.parameter # 
                        SP.line << t!SP.line # SP.role << t!SP.role)
        recToTuple rec = (skel, (read parameter) , line, role)
            where (RecCons skel (RecCons parameter (RecCons line (RecCons role _)))) = 
                      rec RecNil
    in do recs <- myQuery q
          return $ L.map recToTuple recs

showq tTheoryId =
    do t <- table short_profile  -- the query
       restrict ((t!SP.theory_id) .==. (constant tTheoryId))
       project (SP.skeleton_md5 << t!SP.skeleton_md5 # 
                SP.parameter << t!SP.parameter # 
                SP.line << t!SP.line # SP.role << t!SP.role)
