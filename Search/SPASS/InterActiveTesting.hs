{- |
Module      :  $Header$
Description :  Fot testing purpose with GHCI
Copyright   :  (c) Immanuel Normann, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  inormann@jacobs-university.de
Stability   :  provisional
Portability :  portable
-}
{- SoftFOL.DFGParser must export term,
   Search.SPASS.DB must not have Main as module name
-}
module Main where

import Data.List as L
import Data.Set as S
import Data.Map as M (Map,fromList,toList)
import System.Environment (getArgs)

import Search.Utils.SetMap (fromListSetValues)
import Search.Utils.List (mapShow)

import Search.SPASS.DB hiding (main)
import Search.Common.Data hiding (parameter)
import Search.Common.BooleanRing
import Search.Common.Normalization
import Search.Common.Select hiding (matchSkeleton)
import Search.SPASS.FormulaWrapper
import Search.SPASS.UnWrap hiding (f1,f2)
import Search.SPASS.Cache
import SoftFOL.Sign
import SoftFOL.DFGParser (term)
import Text.ParserCombinators.Parsec

import Database.HaskellDB
import Database.HaskellDB.DriverAPI
import Database.HaskellDB.HDBRec
import Search.DB.Connection
import Search.DB.FormulaDB.Skel_to_theory as T
import Search.DB.FormulaDB.Profile as P hiding (Role,skeleton)

testdfg = "/home/immanuel/dfg/query-files/test.dfg"
tmp = "/home/immanuel/dfg/query-files/tmp.dfg"
tmp2 = "/home/immanuel/dfg/query-files/tmp2.dfg"
alg1 = "/home/immanuel/dfg/query-files/alg_1__t9_alg_1.dfg"
aff1 = "/home/immanuel/dfg/query-files/aff_1__t10_aff_1.dfg"

runOn normalizer file = 
    do (t,_,_):_ <- readDFGFormulae file
       return (normalizer $ wrapTerm t)

elemQ (Binder _ _ f) = elemQ f
elemQ f = f

runTest file = do fs <- readDFGFormulae file
                  mapM_ showAnalyse fs
                  --showAnalyse (fs!!0)
                  --return (map analyse fs)

analyse (t,n,r) = (normalize f,alphaNormalize $ annotateScope f,n::Int,r::Role)
    where f = wrapTerm t

showAnalyse :: (SoftFOL.Sign.SPTerm, Int, Role) -> IO ()
showAnalyse (t,n,r) =
    let (nf,af,n,r) = analyse (t,n,r)
    in do putStrLn "8<------------------------------------------"
          -- putStrLn ("line: " ++ show n) -- ++ "  role: " ++ show r)
          putStrLn (show nf)
          putStrLn (show af)

f1 = "forall([a,b],and(a,or(b,not(a))))"
f2 = "implies(P(A),implies(R(B,A),Q(B)))"
f3 = "forall([A],implies(P(A),forall([B],implies(R(B,A),Q(B)))))"
f4 = "implies(f1(A),implies(f2(B,A),and(f3(B),and(f4(B),f5(B)))))"

br str = getTerm str >>= return . brForm
{-
*SPASS.InterActiveTesting> br "implies(a,b)"
(xor "a" (and "b" "a") true)
-}

getTerm str = run term str >>= return . wrapTerm
getBTerm str = run term str >>= return . fromAlgebra . wrapTerm
reduceBTerm str = run term str >>= return . reduce . fromAlgebra . wrapTerm

getArguments (Var _ args) = args
getArguments (Const _ args) = args

run p input = case (parse p "" input)
              of Left err -> error (show err)
                 Right result  -> return result

-- --------------------------------------------------------------
{-
search getSourceProfiles dir file =
    let skelOf (skel,_,_,_) = skel
    in do (axioms,theorems) <- getSourceProfiles dir file
          axioms' <- return $ removeDuplicateProfiles axioms
          targetCandidates <- allTargetCandidates (L.map skelOf axioms')


allTargetCandidates skels =
    let len = length $ nub skels
        comprisesAllSkels skelLineSet = 
                     ((S.size $ S.map fst skelLineSet) == len)
    in do triples <- matchSkeleton skels
          return $ (M.map fromSetSetValues
                         (M.filter comprisesAllSkels (fromListSetValues triples)))

dfgNormalize (lib,theory) (spterm, lineNr, role) = 
    Profile lib theory lineNr spterm skel pars role strength
         where (skel,pars,strength) = normalize $ wrapTerm spterm

-}

dfgProblems = "/home/immanuel/dfg/dfg-problems"
gs f = getAxiomSkels dfgProblems f
--alg1 =  "alg_1/alg_1__t9_alg_1.dfg"

getAxiomSkels :: DirPath -> FileName -> IO [Skel]
getAxiomSkels dir file =
    let getSkel (skel,_,_,_) = skel
    in do (axioms,_) <- readAxiomsAndTheorems dir file
          return $ L.map getSkel axioms

--getTheoryIds :: [Skel] -> IO (M.Map TheoryName (S.Set Skel))
getTheoryIds skels =
    let q = do t <- table profile  -- the query
	       restrict (_in (t!P.skeleton_md5) (L.map constant skels))
	       project (file << t!file # P.skeleton_md5 << t!P.skeleton_md5)
        recToTuple rec = (theory,skel)
            where (RecCons theory (RecCons skel _)) = rec RecNil
        recsToMap recs = L.map recToTuple recs
        --recsToMap recs = fromListSetValues $ L.map recToTuple recs
    in do recs <- myQuery q
          return $ recsToMap recs


--fromListSetValues :: (Ord k,Ord v) => [(k,v)] -> Map.Map k (Set.Set v)

boese = "1a8c5f73411bbd689bff1d9306b9da3b"
gut = "000014d104f7cccb8a8bf6471f220f0a"

main = do args <- getArgs
          case args of
            ("skel":skel:_) -> getTheoryIds [skel] >>= putStrLn . show
            ("file":file:_) -> getAxiomSkels dfgProblems file >>= 
                               getTheoryIds >>=
                               putStrLn . show

{-
  ab hier interessant:
-}
serialize skel =
    let q = do t <- table skel_to_theory  -- the query
               restrict ((t!T.skeleton_md5) .==. (constant skel))
	       project (theory_id << t!theory_id)
        recToTuple rec = skel
            where (RecCons skel _) = rec RecNil
        recsToSet recs = S.fromList $ L.map recToTuple recs
        --recsToMap recs = fromListSetValues $ L.map recToTuple recs
    in do recs <- myQuery q
          putStrLn skel
          writeFile ("/home/immanuel/dfg/cache/" ++ skel) (show $ recsToSet recs)
          --serialize 0 $ recsToMap recs

s1 = ["d304fdc9ed308dcf598ea4361eb69340","1a8c5f73411bbd689bff1d9306b9da3b","e1c12f1b37171c29b65ba1230072e10f"]

readIntList lst = (read lst)::[Int]
readIntSet lst = (read lst):: S.Set Int
readStrList lst = (read lst)::[String]

readTheoryIds skel = readFile ("/home/immanuel/dfg/cache/" ++ skel) >>= return . readIntSet

readAllSkeletons = readFile "/home/immanuel/dfg/cache/all-skeletons" >>= return . readStrList

readTheoryIdIntersection skels = 
    do listOfTids <- mapM readTheoryIds skels
       return $ S.size $ L.foldl1 S.intersection listOfTids

-- readTheoryIdIntersection ["a","b","c","d","e","f","g","h","i","j"]

showSQL = do t <- table skel_to_theory  -- the query
             restrict ((t!T.skeleton_md5) .==. (constant "1a8c5f73411bbd689bff1d9306b9da3b"))
	     project (theory_id << t!theory_id)

{-
serialize n [] = return ()
serialize n assoc = 
    let step = 5
        (l,rassoc) = splitAt step assoc
        lassoc = M.toList $ fromListSetValues l
    in do writeFile ("/home/immanuel/dfg/cache/" ++ show n) $ show lassoc
          putStrLn $ show n
          serialize (n+step) rassoc

genCache = getTheoryIds4 $ take 12 skels
-}

targetCandidates :: [String] -> S.Set Int
targetCandidates skels = foldr1 S.intersection filteredTidsList
    where inSkels (s,_) = elem s skels
          filteredTidsList = L.map snd $ L.filter inSkels cache



{- alternative Ansaetze

targetCandidates skels = M.fold S.intersection (M.filter inSkels cache)
    where inSkels s _ = s elem skels
          
foldWithKey :: (k -> a -> b -> b) -> b -> Map k a -> b
 keys map = foldWithKey (\k x ks -> k:ks) [] map
filterWithKey :: Ord k => (k -> a -> Bool) -> Map k a -> Map k a

conditionalIntersect :: String -> S.Set Int -> S.Set Int -> S.Set Int
conditionalIntersect skel tids1 tids2 =
    if skel in skels
    then S.intersect tids1 tids2
    else 

-}                        


{-
 CACHE
-}
