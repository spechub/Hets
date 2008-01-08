{- |
Module      :  $Header$
Description :  Fot testing purpose with GHCI
Copyright   :  (c) Immanuel Normann, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  inormann@jacobs-university.de
Stability   :  provisional
Portability :  portable
-}
module Search.Main where
--module SPASS.InterActiveTesting where

import Search.Utils.List (filterNeq,pprintList)
import Search.Common.Normalization
import Search.Common.ACINormalization
import Search.Common.Retrieval
import Search.Common.Matching
import Search.SPASS.FormulaWrapper
import Search.SPASS.Sign
import Search.SPASS.Retrieval (getProfilesFrom,retrieveSpassProfiles,retrieveSpassMorphs)
import Search.SPASS.DFGParser hiding ((<<),formula,constant)
import Text.ParserCombinators.Parsec hiding (Line)

import Database.HaskellDB
import Database.HaskellDB.GenericConnect
import Database.HaskellDB.HDBRec

import DB.Connection
import qualified DB.MPTP.Profile as DB
import MD5 --(md5s,Str)

import Config (dfgQueryFile,dfgHome)
import qualified Common.Matching as Match
import qualified Data.List as L
import qualified Data.Set as S
import qualified Data.Map as M
import System.Environment (getArgs)
import System.Posix.Directory (changeWorkingDirectory,getWorkingDirectory)

--import Common.Intersection -- currently broken

main = do (dir:file:_) <- getArgs 
          --analyzeForTheoremReuse dir file
          retrieve dir file

data Hide a = Hide a
instance Show (Hide a) where
    show a = "habe fertig"


getFormula :: String -> IO (Formula (Constant SpassConst) SPIdentifier)
getFormula f = do spterm <- SPASS.DFGParser.run term f
                  return (wrapTerm spterm)

getFs :: IO [Formula (Constant SpassConst) SPIdentifier]
getFs = procFormulasFromFile dfgQueryFile id

getNfs = do nfsl <- getWith normalize
	    return (filter (/=Const TrueAtom []) (map (theNF . fst) nfsl))

    --where nfsWithoutTrue = (filter (/=Const TrueAtom [])) . (map (theNF . fst)) . normalize

getf :: IO (Formula (Constant SpassConst) SPIdentifier)
getf = getFs >>= (return . head)

getnf :: IO (Formula (Constant SpassConst) Int)
getnf = do f <- getf
	   case normalize f of (nf,_,_) -> return nf

theNF (nf,_,_) = nf

-- hole alle Formeln aus test.dfg und map proc auf diese.
--getWith :: (Formula (Constant SpassConst) SPIdentifier -> c) -> IO [(c,String)]
getWith proc = procNamedFormulasFromFile dfgQueryFile proc

procFormulasFromFile :: SourceName -> (Formula (Constant SpassConst) SPIdentifier -> c) -> IO [c]
procFormulasFromFile path proc =
    do result <- parseFromFile parseSPASS path
       case result of Left err  -> error (show err)
		      Right spproblem  -> do return (getFormulas proc spproblem)

procNamedFormulasFromFile :: SourceName -> (Formula (Constant SpassConst) SPIdentifier -> c) -> IO [(c,Int)]
procNamedFormulasFromFile path proc =
    do result <- parseFromFile parseSPASS path
       case result of Left err  -> error (show err)
		      Right spproblem  -> do return (getNamedFormulas proc spproblem)

getBody (Binder _ _ b) = getBody b
getBody f = f


getFormulas proc spproblem = map (proc . wrapTerm . sentence) spformulas
    where (SPProblem _ _ (SPLogicalPart _ _ flsts) _) = spproblem
          spformulas = concatMap (\(SPFormulaList _ f) -> f) flsts

getNamedFormulas :: (Formula (Constant SpassConst) SPIdentifier -> b)
		 -> SPProblem
		 -> [(b, Int)]
getNamedFormulas proc spproblem = map procNamedFormula spformulas
    where (SPProblem _ _ (SPLogicalPart _ _ flsts) _) = spproblem
          spformulas = concatMap (\(SPFormulaList _ f) -> f) flsts
	  procNamedFormula spformula = (proc $ wrapTerm $ sentence spformula, read $ senName spformula)
{-
getNfsAndProfiles :: IO [(Formula (Constant SpassConst) Int, Match.Profile Int SPIdentifier ([Char], Int))]
getNfsAndProfiles =
    do namedFormulas <- getWith normalize
       return (getPs 1 namedFormulas)
	   where getPs _ [] = []
		 getPs nr (naf:nafs) = (namedFormulaToNfAndProfile nr naf):getPs (nr+1) nafs


namedFormulaToNfAndProfile nr ((nf,params,_),line) = (nf,Match.NF nr params ("test.dfg",line))
-}

getProfiles dir file = 
    do namedFormulas <- procNamedFormulasFromFile (dir ++ "/" ++ file) normalize
       return (map namedFormulaToProfile namedFormulas)
           where namedFormulaToProfile ((sid,params,_),line) = Match.Profile file line sid params

{-
selectProfileById :: [Int] -> [Profile t Int sid p] -> [Profile t Int sid p]
selectProfileById lst (p:ps) = if elem ((formulaId p)::Int) lst then p:(selectProfileById lst ps) else (selectProfileById lst ps)
selectProfileById _ [] = []


intersectFiles dir file1 file2 =
    do profiles1 <- getProfiles dir file1
       profiles2 <- getProfiles dir file2
       return (intersectProfiles profiles1 profiles2)
-}
-- some test formulas
assoc = getFormula "forall([a,b,c],equal(f(a,g(b,c)),f(g(a,b),c)))." -- 11 Vorkommen
absorbtion = getFormula "forall([a,b],equal(cup(a,cap(a,b)),a))." -- 17 Vorkommen

{-
*Main> intersectFiles "/home/immanuel/dfg/ring-abel.dfg" "/home/immanuel/dfg/ring-eins.dfg"
[(fromList [(("/home/immanuel/dfg/ring-abel.dfg",13),("/home/immanuel/dfg/ring-eins.dfg",13)),(("/home/immanuel/dfg/ring-abel.dfg",14),("/home/immanuel/dfg/ring-eins.dfg",13)),(("/home/immanuel/dfg/ring-abel.dfg",15),("/home/immanuel/dfg/ring-eins.dfg",15)),(("/home/immanuel/dfg/ring-abel.dfg",16),("/home/immanuel/dfg/ring-eins.dfg",15)),(("/home/immanuel/dfg/ring-abel.dfg",17),("/home/immanuel/dfg/ring-eins.dfg",16)),(("/home/immanuel/dfg/ring-abel.dfg",18),("/home/immanuel/dfg/ring-eins.dfg",17)),(("/home/immanuel/dfg/ring-abel.dfg",19),("/home/immanuel/dfg/ring-eins.dfg",19))],fromList [("0","1"),("mult","plus"),("plus","mult")])]

removeTrueAtoms namedFormulas = filter isNotTrueAtom namedFormulas
    where isNotTrueAtom ((Const TrueAtom [],_,_),_) = False
	  isNotTrueAtom _ = True
-}



{- XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX -}


retrieve :: FilePath -> String -> IO (Hide (M.Map Theory [ProfileMorphism FormulaId String]))
retrieve dir file = retrieveSpassMorphs dir file >>= analyze >>= return . Hide

{- test:
Hide r <- retrieve dfgHome "zfmisc_1__t2_zfmisc_1.dfg"
-}

analyze :: M.Map Theory [ProfileMorphism FormulaId String]
        -> IO (M.Map Theory [ProfileMorphism FormulaId String])
analyze morphMap = 
    let morphList = M.toList morphMap
        targetTheories = L.nub $ map fst morphList
        nrOfTargetTheories = length targetTheories
    in do putStrLn ("Number of target theories: " ++ (show nrOfTargetTheories))
          putStrLn "Target theories: "
          putStrLn $ show targetTheories
          putStrLn "\nProfile morphisms: "
          putStrLn $ concatMap showPMorph morphList
          return morphMap

showPMorph :: (Theory,[ProfileMorphism FormulaId String]) -> String
showPMorph (theory,pMorphs) = "\n\nTarget theory: " ++ theory ++ "\n" ++ concatMap showPm sortedPMorphs
        where showPm (fidMap,pMap) = "\n" ++ (show $ filterNeq $ M.toList fidMap) ++ "\n" ++ (show $ M.toList pMap) ++ "\n"
              sortedPMorphs = sortPMorphs $ pMorphs
              sortPMorphs = L.sortBy compareParameter
              compareParameter pm1 pm2 = compare (M.size $ snd pm2) (M.size $ snd pm1)


-- Don't use the hack below unless you know what you are doing!!
-- variant of retrieveSpassMorphs from SPASS/Retrieval.hs
{-
type ProfileMorphism s p = (FormulaIdMap s,ParameterMap p)
type FormulaIdMap fid = M.Map fid fid
type ParameterMap p = M.Map p p

-}
analyzeForTheoremReuse dir file =
    let sourceTheoremMd5 sourceTheoremProfile = md5s $ Str $ show $ skeleton sourceTheoremProfile
        sourceTheoremProfileMd5 sourceTheoremProfile =
            Profile (theory sourceTheoremProfile)
                    (formulaId sourceTheoremProfile)
                    (sourceTheoremMd5 sourceTheoremProfile)
                    (parameter sourceTheoremProfile)
        nra (_,nra',_,_) = nra'
        nrr (_,_,nrr',_) = nrr'
        nrOfAugmentingProfileMorphs recs = foldl (+) 0 (map nra recs)
        nrOfRedundantProfileMorphs recs = foldl (+) 0 (map nrr recs)
    in do (profileMorphs,sourceTheoremProfile) <- retrieveMorphisms' (getProfilesFrom dir file)
          recs <- mapM (qualifyTheorems' sourceTheoremProfile) (M.toList profileMorphs)
          putStrLn ("Source theory: " ++ file)
          putStrLn ("Number of morphisms yielding reusable theorems: " ++ (show $ nrOfAugmentingProfileMorphs recs))
          putStrLn ("Number of morphisms yielding no reusable theorems: " ++ (show $ nrOfRedundantProfileMorphs recs))
          putStrLn "\n"
          --pprintList recs
          putStrLn "\n\n"
          return (Hide recs)

{- Note this hack below: with (init tps) and (last tps) separate axioms and the conjecture.
   This hack works only for the mptp library where in each file the last formula is the conjecture
   whereas the rest are axioms.
-}
retrieveMorphisms' getProfiles = 
    do (theorem,sps,tps) <- retrieveSource' getProfiles
       pms <- return (profileMorphs (init sps) tps) 
       return (pms,theorem)

retrieveSource' getProfiles =
    do profiles <- getProfiles
       let nonTrivialProfiles = removeTrueAtoms $ profiles
           axioms = init nonTrivialProfiles
           theorem = last nonTrivialProfiles
	   (md5s,sourceProfiles) = toMd5sAndProfiles $ sortProfiles axioms
	   in do targetProfiles <- retrieveProfiles md5s
		 return (theorem,sourceProfiles,targetProfiles)

qualifyTheorems' sourceTheoremProfile (target,profileMorphs) =
    do --putStrLn ("target: " ++ target)
       recs <- retrieveProfiles' target
       targetProfiles <- return (map recToProfile' recs)
       ((nra,a),(nrr,r)) <- return (analyzeTarget target sourceTheoremProfile targetProfiles profileMorphs)
       return $ (target,nra,nrr,(a,sourceTheoremProfile)) --,Hide ((targetProfiles, profileMorphs),(a,r)))


analyzeTarget target sourceTheoremProfile targetProfiles profileMorphs =
    let sourceTheoremMd5 = md5s $ Str $ show $ skeleton sourceTheoremProfile
        sourceTheoremParams = parameter sourceTheoremProfile
        --md5Match targetProfile = sourceTheoremMd5 == (skeleton targetProfile)
        --md5MatchingTargets =  filter md5Match targetProfiles
        paramMatch profileMorph targetProfile = 
            sourceTheoremParams == applyMorph (snd profileMorph) (parameter targetProfile) &&
            sourceTheoremMd5 == (skeleton targetProfile)
        redundantTheorems pm = (filter (paramMatch pm) targetProfiles,pm)
        hasRedundantTheorem (rts,_) = not $ null rts
        allRedundantTheorems = map (fidIt . redundantTheorems) profileMorphs
        (badPms,goodPms) = L.partition hasRedundantTheorem allRedundantTheorems
        fidIt (tp,pm) = (map formulaId tp,pm)
        redundantProfileMorphs = badPms
        augmentingProfileMorphs = goodPms
    in (((length augmentingProfileMorphs),augmentingProfileMorphs),
        ((length redundantProfileMorphs), redundantProfileMorphs))
    --in (nrOfAugmentingProfileMorphs,nrOfRedundantProfileMorphs,augmentingProfileMorphs,redundantProfileMorphs)
    --in (target, sourceTheoremProfile,profileMorphs)

type ProfileMorphisms = (ProfileMorphism Theory String)

--reallyAugmenting :: String -> [([FormulaId], ProfileMorphisms)] -> [([FormulaId], ProfileMorphisms)]
reallyAugmenting sourceMd5 xpms = reallyAugmentingPms
    where  wrap (fids,pms) = TPM fids sourceMd5 pms
           tpms = S.fromList $ map wrap xpms
           unwrap (TPM fids _ pm) = (fids,pm)
           reallyAugmentingPms = map unwrap (S.toList tpms)


--tmp =  snd $ snd $ analyzeTarget 1 emptyProfile [] []
emptyProfile = Profile 1 1 1 []
data TpmProfileMorphisms theories fid string = TPM [theories] String (ProfileMorphism fid string) deriving (Eq)


instance (Ord t,Ord f, Ord s) => Ord (TpmProfileMorphisms t f s) where
   compare (TPM _ sourceMd51 (target1,paramMap1)) (TPM _ sourceMd52 (target2,paramMap2)) =
       case (compare sourceMd51 sourceMd52)
       of EQ -> EQ
          _ -> compare target1 target2


applyMorph' pm ps = applyMorph ps pm

retrieveProfiles' theory =
    do withDB $ do t <- table DB.profile
                   restrict (t!DB.file .==. (constant theory))
                   project (DB.file << t!DB.file #
			    DB.line << t!DB.line #
			    DB.skeleton_md5 << t!DB.skeleton_md5 #
			    DB.parameter << t!DB.parameter)


recToProfile' rec = Profile file line smd5 params
    where (RecCons file (RecCons line (RecCons smd5 (RecCons paramStr _)))) = rec RecNil
	  params = (read paramStr)::[String]

recToLineParams rec = (line,parameter)
    where (RecCons line (RecCons parameter _)) = rec RecNil


qualifyTheorems sourceTheoremProfile (target,profileMorphs) = 
    do putStrLn ("Theorem reuse in target theory: " ++ target)
       mapM (qualifyTheorems1 target sourceTheoremProfile) profileMorphs

qualifyTheorems1 target sourceTheoremProfile profileMorph = -- target = file name of the target theory
    let (_,parameterMap) = profileMorph
        morphedParams = applyMorph parameterMap (parameter sourceTheoremProfile)
        skel_md5 = md5s $ Str $ show $ skeleton sourceTheoremProfile
    in do recs <- retrieveSen target skel_md5 morphedParams
          lines <- return (map recToLine recs) -- lines are those where the reused theorem already appear in the target
          return (case lines
                  of [] -> handleReusedTheorem target profileMorph sourceTheoremProfile
                     lines -> handleRedundantTheorems lines target (theory sourceTheoremProfile))

handleReusedTheorem target profileMorph sourceTheoremProfile =
    do putStrLn ("\n\nReused Theorems in " ++ target ++ ":\n" ++ (show $ skeleton sourceTheoremProfile))
       putStrLn ("\n" ++ show profileMorph)

handleRedundantTheorems lines target source = 
    do putStrLn ("\n\nRedundant Theorems in " ++ target ++ ":\n")
       print lines

recToLine rec = line
    where (RecCons line _) = rec RecNil

retrieveSen theory skel_md5 morphedParams =
    do withDB $ do t <- table DB.profile
                   restrict (t!DB.skeleton_md5 .==. (constant skel_md5) .&&.
                             t!DB.file .==. (constant theory) .&&. 
                             t!DB.parameter .==. (constant $show morphedParams))
                   project (DB.line << t!DB.line)

applyMorph parameterMap [] = []
applyMorph parameterMap (p:ps) =
    case (M.lookup p parameterMap)
    of (Just q) -> q:(applyMorph parameterMap ps)
       Nothing -> p:(applyMorph parameterMap ps)

--------------

spl f = do recs <- selectSkeletonParamsLine f
           return $ Hide (map recToSPL recs)

recToSPL rec = (line,skel,param)
    where (RecCons line(RecCons skel (RecCons param _))) = rec RecNil

selectSkeletonParamsLine f =
    do withDB $ do t <- table DB.profile
		   restrict (t!DB.file .==. (constant f) .&&.
                             t!DB.skeleton .<>. (constant "true"))
		   project (DB.skeleton_md5 << t!DB.skeleton_md5 #
			    DB.parameter << t!DB.parameter #
                            DB.line << t!DB.line)



{-
retrieveAndAnalyze :: SourceName -> IO ([Analysis], [Analysis])
retrieveAndAnalyze source = 
    do morphs <- retrieveMorphisms (getAxiomProfilesFrom source)
       (itself,others) <- return $ analyze source morphs
       putStrLn ("Number of theory inclusions to of files: " ++ show (length others))
       pprintList itself
       pprintList others
       return (itself,others)
-}

{-

getAxiomProfilesFrom dir file = -- Vorsicht hack: Annahme ist, dass alle Formeln bis auf die letzte Axiome sind!!!
    do pwd <- getWorkingDirectory
       changeWorkingDirectory dfgHome
       profiles <- getProfilesFrom dir file
       axioms <- return $ sortProfiles $ removeTrueAtoms $ dropLast profiles -- hier ist der hack in dropLast
       changeWorkingDirectory pwd
       print pwd
       return axioms

dropLast lst = init lst

-- variant of 'retrieveSource' from  Common/Retreival.hs
retrieveTmp source = -- Vorsicht hack: Annahme ist, dass alle Formeln bis auf die letzte Axiome sind!!!
    do profiles <- getProfiles dfgHome  source
       let axioms = sortProfiles $ removeTrueAtoms $ dropLast profiles  -- hier ist der hack in dropLast
           --nonTrivialProfiles = sortProfiles $ removeTrueAtoms profiles --namedFormulas
	   (md5s,sourceProfiles) = toMd5sAndProfiles axioms -- nonTrivialProfiles
	   in do targetProfiles <- retrieveProfiles md5s
                 morphs <- return $ profileMorphs sourceProfiles targetProfiles

                 (itself,others) <- return $ analyze source morphs
                 putStrLn ("Number of theory inclusions of other files: " ++ show (length others))
                 putStrLn ("from itself:" ++ source)
                 pprintList itself
                 putStrLn "from others:"
                 pprintList others
		 return $ Hide morphs
                 -- (nonTrivialProfiles,sourceProfiles,targetProfiles)
-}

-- variant of 'retrieveSource' from  Common/Retreival.hs
--retrievePros :: FilePath ->IO (Hide ([Profile Theory Int Int String],[Profile Theory Int Int String]))
{-
retrievePros source = -- Vorsicht hack: Annahme ist, dass alle Formeln bis auf die letzte Axiome sind!!!
    do profiles <- getProfiles dfgHome  source
       let axioms = sortProfiles $ removeTrueAtoms $ dropLast profiles  -- hier ist der hack in dropLast
	   (md5s,sourceProfiles) = toMd5sAndProfiles axioms -- nonTrivialProfiles
	   in do targetProfiles <- retrieveProfiles md5s
                 return $ Hide (sourceProfiles,targetProfiles)
-}

