{- |
Module      :  $Header$
Description :  Interface for SPASS morphism search
Copyright   :  (c) Immanuel Normann, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  inormann@jacobs-university.de
Stability   :  provisional
Portability :  portable
-}
module Search.Main where
--module SPASS.Retrieval where

import Config (dfgQueryFile)
import Data.Map (Map)
import Data.Set (Set)
import Search.Common.Normalization 
import Search.Common.Matching
import Search.Common.Retrieval
import Search.SPASS.Sign
import Search.SPASS.FormulaWrapper
import Search.SPASS.DFGParser hiding ((<<),formula,constant)
import Text.ParserCombinators.Parsec hiding (Line)
import System.Environment (getArgs)

main = do (dir:file:_) <- getArgs
          --morphs <- retrieveSpassMorphs dir file
          morphs <- recordSpassMorphs dir file
          print morphs
          return ()

type URI = String


data Hide a = Hide a
instance Show (Hide a) where
    show a = "habe fertig"

{- test:
let d = "/home/inormann/dfg/dfg-problems/aff_1" 
let f = "aff_1__t11_aff_1.dfg"
-}
-- ** Source File Parsing

recordSpassMorphs :: FilePath -> FilePath -> IO (Map URI [ProfileMorphism Int [Char]])
recordSpassMorphs dir file = recordMorphisms file (getAxiomProfilesFrom dir file)

{- |
   retrieveSpassMorphs takes the 'dfgQueryFile' (s.Config) as query source and returns all profile morphisms
   from including target theories.
--retrieveSpassMorphs :: FilePath -> IO [ProfileMorphism (String, Int) [Char]]
-}
retrieveSpassMorphs :: FilePath -> FilePath ->  IO (Map URI [ProfileMorphism FormulaId String])
retrieveSpassMorphs dir file = 
    do --profiles <- retrieveSpassProfiles dir file
       morphs <- retrieveMorphisms (getAxiomProfilesFrom dir file)
       return morphs

{- |
   retrieveSpassProfiles takes 'dfgQueryFile' (s.Config) as query source and returns 
   the triple of the skeleton profiles of the source, the number profile from the source,
   and the number profile from the target.
-}
retrieveSpassProfiles ::
    FilePath 
    -> String
    -> IO ([Profile FilePath Int (Skeleton SpassConst) [Char]], -- ^ Profiles of the source with skeletons
	   [Profile FilePath Int Int [Char]],  -- ^ Profiles of the source with numbers n referencing the n-th skeleton from the source
	   [Profile FilePath Int Integer String])               -- ^ Profiles of the target with numbers n referencing the n-th skeleton from the source

retrieveSpassProfiles dir file = retrieveSource (getProfilesFrom dir file)

getNamedFormulas :: (Formula (Constant SpassConst) SPIdentifier -> b) -> SPProblem -> [(b, Int)]
getNamedFormulas proc spproblem = map procNamedFormula spformulas
    where (SPProblem _ _ (SPLogicalPart _ _ flsts) _) = spproblem
          spformulas = concatMap (\(SPFormulaList _ f) -> f) flsts
	  procNamedFormula spformula = (proc $ wrapTerm $ sentence spformula, read $ senName spformula)

procNamedFormulasFromFile :: SourceName -> (Formula (Constant SpassConst) SPIdentifier -> c) -> IO [(c,Int)]
procNamedFormulasFromFile path proc =
    do result <- parseFromFile parseSPASS path
       case result of Left err  -> error (show err)
		      Right spproblem  -> do return (getNamedFormulas proc spproblem)

getProfilesFrom :: FilePath -> String -> IO [Profile FilePath Int (Skeleton SpassConst) SPIdentifier]
getProfilesFrom dir file =
    do namedFormulas <- procNamedFormulasFromFile (dir ++ "/" ++ file) normalize
       return (map namedFormulaToProfile namedFormulas)
	   where namedFormulaToProfile ((nf,params,_),line) = Profile file line nf params

--data StatementType = Axiom | Assertion -- | Definition | Conjecture | Theorem etc. todo: move to Common/?.hs

getAxiomProfilesFrom :: FilePath -> String -> IO [Profile FilePath Int (Skeleton SpassConst) SPIdentifier]
getAxiomProfilesFrom dir file =
    do result <- parseFromFile parseSPASS (dir ++ "/" ++ file)
       case result 
         of Left err  -> error (show err)
	    Right spproblem  -> do return (spassProblemToAxiomProfiles dir spproblem)

-- todo: integrate StatementType into Profile to avoid spagetthi hacks below
spassProblemToAxiomProfiles :: URI
                            -> SPProblem
                            -> [Profile URI Int (Skeleton SpassConst) SPIdentifier]
spassProblemToAxiomProfiles theory sp = profiles
    where (SPProblem _ _ (SPLogicalPart _ _ flsts) _) = sp
          spformulas = concatMap (\(SPFormulaList _ f) -> f) flsts
          xprofiles = map (spassFormulaToProfile theory) spformulas -- hack
          profiles = map fst (filter snd xprofiles) -- hack

spassFormulaToProfile :: URI -> SPFormula -> (Profile URI Int (Skeleton SpassConst) SPIdentifier,Bool)
spassFormulaToProfile theory (NamedSen line isax _ spterm) =
    ((Profile theory (read line) skel plst),isax) -- hack
        where (skel,plst,_) = normalize $ wrapTerm spterm
              --role = if isax then Axiom else Assertion
              
       


{-
data Pofile t fid sid p =
    Profile 
    { theory :: t,    
      formulaId :: fid,
      skeleton :: sid,
      parameter :: [p]
    } deriving (Eq, Ord, Show)

data Named s = NamedSen
    { senName  :: String
    , isAxiom :: Bool
    , isDef :: Bool
    , sentence :: s } deriving (Eq, Ord, Show)

type SPFormula = Named SPTerm


NamedFormula:
(((_Equal (0 0) (0 0)),["k1_zfmisc_1","k1_xboole_0","k1_tarski","k1_xboole_0"],"strong"),165)
-}