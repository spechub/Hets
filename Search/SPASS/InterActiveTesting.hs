{- |
Module      :  $Header$
Description :  Logic independent retrieval functionality
Copyright   :  (c) Immanuel Normann, Uni Bremen 2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  inormann@jacobs-university.de
Stability   :  provisional
Portability :  portable
-}

module Main where

import Search.SPASS.FormulaWrapper (wrapTerm,SpassConst)
import Search.SPASS.UnWrap (readDFGFormulae)
import Search.Common.Normalization (normalize)
import Search.Common.Data hiding (parameter,role)
import Search.SPASS.ByteString
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
--import Search.DB.FormulaDB.Profile as P
import Search.DB.FormulaDB.Short_profile as SP
import SoftFOL.Sign --(SPTerm,)
--import Search.DB.FormulaDB.Skel_to_theory as ST
import Search.DB.FormulaDB.Theory as T
import MD5
import System.Environment (getArgs)
import System.Directory (getDirectoryContents)

dir = "/home/immanuel/dfg/dfg-problems/alg_1"
dfgFile = "alg_1__t9_alg_1.dfg"
--dfgFile = "mod_1__t13_mod_1.dfg"

-- todo: SenType -> Role in ShortProfile

main = do args <- getArgs
          case args of
            ("-db":dir:file:_) -> searchDFG True dir file >> return ()
            (dir:file:_) -> searchDFG False dir file >> return ()
            _ -> error "invalid arguments! It should be one of:\nsearch <dir> <file>"
            

-- -----------------------------------------------------------
-- *  SPASS specific
-- -----------------------------------------------------------

searchDFG :: Bool -> DirPath -> FileName -> IO [[LongInclusionTuple SPIdentifier]]
searchDFG toDB = search toDB readAxiomsAndTheorems

readAxiomsAndTheorems :: DirPath -> FileName -> IO [Triple SpassConst SPIdentifier]
readAxiomsAndTheorems dir file =
    do fs <- readDFGFormulae (dir ++ "/" ++ file) -- fs :: [DFGFormula]
       return $ (L.map toSProfile fs)

type DFGFormula = (SPTerm, LineNr, Search.Common.Data.Role)
-- type ShortProfile p = (Skel, [p], LineNr, SenType)


toSProfile :: (SPTerm, LineNr, Search.Common.Data.Role)
           -> Triple SpassConst SPIdentifier
toSProfile (spterm,line,role) = (formula,line,role')
    where formula = wrapTerm spterm
          --skel' = md5s $ Str $ show $ skel
          role' = if role == Axiom then "axiom" else "theorem"

-- -----------------------------------------------------------
-- *  Principle Functions
-- -----------------------------------------------------------

--test = search' "/home/immanuel/dfg/dfg-problems/alg_1" "alg_1__t9_alg_1.dfg"
--test' "/home/immanuel/dfg/dfg-problems/abcmiz_0" "abcmiz_0__t10_abcmiz_0.dfg"
-- "/home/immanuel/dfg/dfg-problems/bvfunc26" "bvfunc26__t22_bvfunc26.dfg"

test' dir file =
    do triples <- readAxiomsAndTheorems dir file -- (formula,line,role') [ShortProfile p]
       (axioms,theorems) <- return $ L.partition isAxiom $ normalizeAndCleanUp triples
       --tIds <- targetIds $ L.map getSkel axioms  -- [Int]
       tIdSets <- mapM readTheoryIds $ L.map getSkel axioms
       return $ (H tIdSets,L.map S.size tIdSets)

search :: (Show p, Show c, Ord p, Ord c, Read p) =>
           Bool
          -> (DirPath -> TheoryName -> IO [Triple c p])
          -> DirPath
          -> TheoryName
          -> IO [[LongInclusionTuple p]]
search toDB getSourceProfiles dir file =
    do triples <- getSourceProfiles dir file -- (formula,line,role') [ShortProfile p]
       (axioms,theorems) <- return $ L.partition isAxiom $ normalizeAndCleanUp triples
       skels <- return $ L.map getSkel axioms
       tIds <- theoryIdsIntersection skels 
       theoryIdNamePairs <- idToName tIds
       mapM (matchOne toDB skels axioms theorems file) theoryIdNamePairs

idToName :: [TargetId] -> IO [(TargetId,TheoryName)]
idToName theoryIds =
    let q = do t <- table theory  -- the query
	       restrict (_in (t!T.tid) (L.map constant theoryIds))
	       project (T.tid << t!T.tid # T.name << t!T.name)
        recToTuple rec = (id,name)
            where (RecCons id (RecCons name _)) = rec RecNil
        recsToMap recs = L.map recToTuple recs
    in do recs <- myQuery q
          return $ recsToMap recs

-- type LongInclusionTuple p = (TheoryName, TheoryName, Renaming p, LineMap, [LineNr])


matchOne :: (Read p,Ord p,Show p) => Bool -> [Skel] -> [ShortProfile p] -> [ShortProfile p]
         -> TheoryName -> (TheoryId,TheoryName)
         -> IO [LongInclusionTuple p]
matchOne toDB skels sAxioms sTheorems sTheoryName (tTheoryId,tTheoryName) =
    let toIncTuple (st,tt,ps,lm,lines) =  (st,tt,ps,lm,length lines)
    in do putStrLn tTheoryName
          targetProfiles <- getProfilesFromDB tTheoryId skels
          morphs <- return $ theoryInterpretation sAxioms targetProfiles
          longIncTuples <- return (L.map (inclusionTuple sTheoryName tTheoryName
                                          targetProfiles sTheorems)
                                   morphs)
          if toDB
            then do multiInsertInclusion $ (L.map toIncTuple longIncTuples)
                    return longIncTuples
            else return longIncTuples



toProfile2 (skel, ps, lineNr, _) = (skel, (ps, lineNr))

type TargetId = Int

data Hide x = H x


targetIds :: [Skel] -> IO [TargetId]
targetIds skels =
    do targetIdMatrix <- mapM readTheoryIds skels
       return $ S.toList $ foldr1 S.intersection $
              L.sortBy compSetSize targetIdMatrix

compSetSize :: Set Int -> Set Int -> Ordering -- for descending sortBy !!!
compSetSize s1 s2 = compare (S.size s2) (S.size s1)




-- skel: "000014d104f7cccb8a8bf6471f220f0a"
skel_cache_file = "/home/immanuel/dfg/skel-cache"

writeClassifiedTheoryIdSet :: Skel -> IO ()--TheoryIds

writeSkelCache :: IO ()
writeSkelCache =
    do (_:_:skels) <- getDirectoryContents "/home/immanuel/dfg/cache" 
       writeFile skel_cache_file "skelCache = ["
       mapM writeClassifiedTheoryIdSet skels
       appendFile skel_cache_file "]"


writeClassifiedTheoryIdSet skel =
    let classify tids = if S.size tids < 2000
                        then TIds (skel,(True,(S.size tids,tids)))
                        else TIds (skel,(False,(S.size tids,(complement tids))))
    in do putStrLn skel
          tids <- readTheoryIds skel
          appendFile skel_cache_file ("  " ++ (show $ classify tids) ++ ",\n")

readTheoryIds :: Skel -> IO (Set Int)
readTheoryIds skel = readFile ("/home/immanuel/dfg/cache/" ++ skel) >>= return . readIntSet

readIntSet str = (read str)::S.Set Int

allTids = S.fromList [1..41758]

complement :: Set Int -> Set Int
complement = S.difference allTids

data TheoryIds = TIds (Skel,(Bool,(Int,(Set Int)))) deriving Show


s16 = "00070b01ff9f0d8635d47dab235f8f8f"
s5101 = "0009fa10450577924b70d4978e5bf4ef"

{-

  TIds ("9f389b080cbea52db3851ec2a523464b",(True,(3,fromList [21134,21135,21159]))),

  TIds ("fe69886c6b8c727abfed03f1e0c391fd",(True,(2,fromList [21159,36437]))),

*Main> theoryIdsIntersection ["9f389b080cbea52db3851ec2a523464b","fe69886c6b8c727abfed03f1e0c391fd"]
[21159]

-}

theoryIdsIntersection :: [Skel] -> IO [Int]
theoryIdsIntersection skels =
    do bstrs <- mapM readTheorIdByteString skels
       return $ fromByteString $ multiply bstrs

--theorIdByteStringIntersection bstrs = multiply bstrs

--readTheorIdByteString :: Skel -> Data.ByteString.Internal.ByteString
readTheorIdByteString skel = 
    readByteString ("/home/immanuel/dfg/bytestring-cache/" ++ skel)



genByteCache :: IO ()
genByteCache =
    do (_:_:skels) <- getDirectoryContents "/home/immanuel/dfg/cache"
       mapM_ genByteCache1 skels


genByteCache1 :: Skel -> IO ()
genByteCache1 skel =
    do putStrLn skel
       str <- readFile ("/home/immanuel/dfg/cache/" ++ skel)
       writeIntList ("/home/immanuel/dfg/bytestring-cache/" ++ skel) $
                    S.toAscList $ readIntSet str

genCocache :: Skel -> IO ()
genCocache skel =
    do str <- readFile ("/home/immanuel/dfg/cache/" ++ skel)
       writeFile ("/home/immanuel/dfg/cocache/" ++ skel)
                     (show $ S.toList $ complement $ readIntSet str)

theoryIdsFromCocache :: Skel -> IO [Int]
theoryIdsFromCocache skel = readFile ("/home/immanuel/dfg/cocache/" ++ skel) >>=
                            return . readIntList
    where readIntList str = (read str)::[Int]

-- type ShortProfile p = (Skel, [p], LineNr, SenType)
isAxiom (_,_,_,r) = r == "axiom"
getSkel (skel,_,_,_) = skel
getRen (_,ren,_,_) = ren
getLine (_,_,line,_) = line

type Triple c p = (Search.Common.Data.Formula (Constant c) p, LineNr, SenType)

--normalizeAndCleanUp :: (Eq p) => [ShortProfile p] -> [ShortProfile p]
normalizeAndCleanUp :: (Show p, Show c, Ord p, Ord c) =>
                       [Triple c p] -> [ShortProfile p]
normalizeAndCleanUp triples = L.map normalizeTriple cleanTriples
    where isNonTrivial ((Const TrueAtom []),_,_) = False
          isNonTrivial _ = True
          eqTriples (f1,_,_) (f2,_,_) = f1 == f2
          cleanTriples = nubBy eqTriples $ L.filter isNonTrivial triples
          normalizeTriple (f,l,r) = (md5s $ Str $ show s,p,l,r)
              where (s,p,_) = normalize f


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

-- -----------------------------------------------------------
-- *  Matching
-- -----------------------------------------------------------

theoryInterpretation :: (Read p, Ord p) => [ShortProfile p] -> [ShortProfile p]
                     -> [(Renaming p, LineMap)]
theoryInterpretation sAxioms tProfiles = 
    case (L.map (matchList tProfiles) sAxioms)
    of [] -> []
       matrix ->  foldl1 merge (L.sortBy compListLength matrix) -- sort improves speed!


compListLength :: [a] -> [a] -> Ordering
compListLength s1 s2 = compare (L.length s1) (L.length s2)


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
            [ShortProfile p] -> ShortProfile p -> [(Renaming p, LineMap)]
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
match :: (Ord p, Read p) => ShortProfile p -> ShortProfile p
                -> Maybe (Renaming p, LineMap)
match (s1,p1,l1,_) (s2,p2,l2,_) =
    if s1 == s2
    then case constructRenaming p1 p2
         of (Just renaming) -> Just (renaming, M.singleton l1 l2)
            _ -> Nothing
    else Nothing

{- |
   constructRenaming takes two lists of parameters and returns (Just) a pointwise
   mapping between these lists if this is consistently possible.
   Otherwise it returns Nothing.
-}
constructRenaming :: (Ord p, Read p) => [p] -> [p] -> Maybe (Renaming p)
constructRenaming lst1 lst2 = SM.fromList $ zip lst1 lst2

