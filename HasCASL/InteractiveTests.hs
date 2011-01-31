{-# LANGUAGE TypeSynonymInstances, Rank2Types #-}
{- |
Module      :  $Header$
Description :  Test functions for MatchingWithDefinitions
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  experimental
Portability :  portable

Test functions for MatchingWithDefinitions
-}

module HasCASL.InteractiveTests where


import HasCASL.Subst
import HasCASL.PrintSubst
import HasCASL.MatchingWithDefinitions ( initialDefStore
                                       , gsymToSym
                                       , matchSpecs
                                       , matchCandidates
                                       , getCandidates
                                       , getMatchResult
                                       , MatchResult(..)
                                       , DefinitionStore
                                       -- , DefStore(..)
                                       )

import HasCASL.As
import HasCASL.Le
import HasCASL.Logic_HasCASL

import Common.AS_Annotation

import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Maybe
import Data.List

import Text.Read


-- global part imports

import Static.SpecLoader (getSigSensComplete, SigSens(..))

import Data.Time.Clock

import Control.Monad
import Control.Monad.Trans (MonadIO (..))

import Driver.Options
import Common.Utils (getEnvDef)
import Common.Doc
import Common.DocUtils


-- For Navigation
import qualified Data.Graph.Inductive.Graph as Graph
import Static.PrintDevGraph()
import Static.DevGraph
import Static.DGNavigation


{- testruns:

-- Use this for new testing:

sigs <- siggy 4

-- match the concrete design to the pattern
testnewM sigs "FlangePattern" "BoltHole" "Durchgangsloch"

testSpecMatchM sigs "FlangePattern" "Component"

fromSigsNiceL sigs "FlangePattern" "Component" allMatches
fromSigsNice sigs "FlangePattern" "Component" (findMatch noConstraints)

-- shortcut for the above statement
matchDesign "/tmp/flange.het" "Match" "FlangePattern" "Component"

-- get the actual parameter spec of FlangePattern
navi sigs $ getActualParameterSpec "FlangePattern"

-- get the local symbols for the actual parameter spec of FlangePattern
naviGen sigs (show . pretty) $ (\ a -> getLocalSyms a $ fst $ fromJust $ getActualParameterSpec "FlangePattern" a)


(res, m1) <- getMatchMap "/tmp/flange.het" "Match" "FlangePattern" "Component"

tmpl <- readFile "/home/ewaryst/Hets-lib/EnCL/flangeExported.het"

writeFile "/tmp/f1.het" $ processTemplate (\ k v -> " . " ++ k ++ " := " ++ show (v * 1000)) m1 tmpl


-}

help :: IO ()
help = do
  s <- readFile "HasCASL/InteractiveTests.hs"
  let l = lines s
      startP = ("{- testruns:" /=)
      endP = ("-}" /=)
  putStrLn $ unlines $ takeWhile endP $ dropWhile startP l


------------------------- Global DG functions -------------------------

-- * Point evaluator

type RealType = Double


{-
type EvalEnv = Map.Map String 

evalInSubst :: Subst -> Term -> RealType
evalInSubst s t =
    case t of
      
    lookupS :: Subst -> a -> Maybe (SRule b)
ruleContent :: SRule a -> a

-}

data Point = P (RealType, RealType, RealType) deriving (Read, Show)
data Vector = V (RealType, RealType, RealType) deriving (Read, Show)

diff :: (Point, Point) -> Vector
diff(p,q) = V(c1(p)-c1(q), c2(p)-c2(q), c3(p)-c3(q))

prod :: (Vector, Vector) -> RealType
prod(V (x1, y1, z1),V (x2, y2, z2)) = x1*x2 + y1*y2 + z1*z2

dist :: (Point, Point) -> RealType
dist(p,q) = sqrt $ prod(diff(p,q), diff(p,q))

diam :: (Point, Point) -> RealType
diam(p,q) = 2*dist(p,q)


c1 :: Point -> RealType
c1 (P (x, _, _)) = x
c2 :: Point -> RealType
c2 (P (_, x, _)) = x
c3 :: Point -> RealType
c3 (P (_, _, x)) = x


type EvalEnv = Map.Map String EvalTerm 

data ETBinFun = ETdiff | ETdiam | ETprod | ETdist deriving Show

data EvalTerm = ETbinary ETBinFun EvalTerm EvalTerm | ETpoint Point
              | ETvector Vector | ETreal RealType | ETconst String deriving Show

toEvalTerm :: Env -> Term -> Maybe EvalTerm
toEvalTerm e t =
    let s = show $ prettyWithAnnos e t
        realL = (reads s) :: [(RealType, String)]
        pointL = (reads s) :: [(Point, String)]
        mT | not (null realL) = Just $ ETreal $ fst $ head realL
           | not (null pointL) = Just $ ETpoint $ fst $ head pointL
           | otherwise = Nothing
    in mT
           

envFromSubst :: Env -> Subst -> EvalEnv
envFromSubst e (Subst (m, _, _)) = Map.fromList $ mapMaybe f $ Map.toList m
    where f (sc, sr) = fmap ((,) $ scName sc) $ toEvalTerm e $ ruleContent sr



etPoint :: EvalTerm -> Point
etPoint (ETpoint p) = p
etPoint et = error $ "etPoint: no point: " ++ show et

etVector :: EvalTerm -> Vector
etVector (ETvector p) = p
etVector et = error $ "etVector: no vector: " ++ show et

etReal :: EvalTerm -> RealType
etReal (ETreal p) = p
etReal et = error $ "etReal: no real: " ++ show et

evalInEnv :: EvalEnv -> EvalTerm -> EvalTerm
evalInEnv e (ETbinary bf t1 t2) =
    let t1' = evalInEnv e t1
        t2' = evalInEnv e t2
    in case bf of
         ETprod -> ETreal $ prod (etVector t1', etVector t2')
         ETdiam -> ETreal $ diam (etPoint t1', etPoint t2')
         ETdist -> ETreal $ dist (etPoint t1', etPoint t2')
         ETdiff -> ETvector $ diff (etPoint t1', etPoint t2')
evalInEnv e (ETconst s) =
    Map.findWithDefault (error $ "evalInEnv: lookup failure for " ++ s) s e
evalInEnv _ x = x


getRconsts :: Env -> Subst -> Map.Map String RealType
getRconsts e s = getRealConstMap e s constsForEval

getRealConstMap :: Env -> Subst -> [(String, EvalTerm)] -> Map.Map String RealType
getRealConstMap e sbst l = Map.fromList $ map f l where 
    ee = envFromSubst e sbst
    f (s, et) = (s, etReal $ evalInEnv ee et)

evalInSubst :: Env -> Subst -> EvalTerm -> EvalTerm
evalInSubst e s t = evalInEnv (envFromSubst e s) t


constsForEval :: [(String, EvalTerm)]
constsForEval =
    [ ("d_0", ETbinary ETdiam (ETconst "BoundaryTube") (ETconst "Offset"))
    , ("d_3", ETbinary ETdiam (ETconst "BoltOffset") (ETconst "Offset"))
    , ("d_4", ETbinary ETdiam (ETconst "BoundaryRing") (ETconst "Offset"))
    , ("d_5", ETbinary ETdiam (ETconst "BoltBoundary") (ETconst "BoltOffset"))
    , ("e_F", ETconst "RingHeight") ]



------------------------- Global DG functions -------------------------

-- * DG Navigation

mkDGNav :: SigSens Env Sentence -> DGNav
mkDGNav s = DGNav (sigsensLibenv s, sigsensDG s, sigsensNode s)


prettyEdge :: DGraph -> Graph.LEdge DGLinkLab -> Doc
prettyEdge dg (n1, n2, dgl) =
    pretty (dgl_id dgl) <> text ":" <+> text (getNameOfNode n1 dg) <+> text "->"
               <+> text (getNameOfNode n2 dg)

prettyNode :: DGraph -> Graph.LNode DGNodeLab -> Doc
prettyNode _ (n, lbl) =
    pretty n <> text ":" <+> text (getDGNodeName lbl)

-- | get all ancestor nodes and output them
collectNodes :: DGraph -> [Graph.Node] -> IO ()
collectNodes _ [] = return ()

collectNodes dg nds = do
  let ledgs = concatMap (innDG dg) nds
      newnds = map linkSource ledgs
      showl = map f ledgs
      f (x, _, lbl) = show x ++ ":" ++ show (pretty $ dgl_origin lbl)
  putStrLn $ show showl
  collectNodes dg newnds


navi :: SigSens Env Sentence
     -> (forall a . DevGraphNavigator a => a -> Maybe (Graph.LNode DGNodeLab))
     -> IO ()
navi s sf = naviGen s pf sf
    where pf x = case x of
                   Just dgn -> show $ prettyNode (sigsensDG s) dgn
                   _ -> error $ "navi: No result."

naviGen :: SigSens Env Sentence -> (b -> String)
     -> (forall a . DevGraphNavigator a => a -> b) -> IO ()
naviGen s pf sf =
    putStrLn $ pf $ sf $ mkDGNav s


naviTest :: SigSens Env Sentence -> String -> IO ()
naviTest sigs s = do
  navi sigs $ getActualParameterSpec s
--  collectNodes (sigsensDG sigs) [sigsensNode sigs]




-- ** Spec extraction

-- see also myHetcatsOpts in Test.hs
myHetsOpts :: HetcatsOpts
myHetsOpts = defaultHetcatsOpts { libdirs = ["../Hets-lib"]
                                , verbose = 0 }

testspecs :: [(Int, (String, String))]
testspecs =
    [ (1, ("HasCASL/Real3D/SolidWorks/Matchtest.het", "Matching1"))
    , (2, ("HasCASL/Real3D/SolidWorks/Matchtest2.het", "Matching0"))
    , (3, ("HasCASL/Real3D/SolidWorks/Matchtest2.het", "Matching1"))
    , (4, ("HasCASL/Real3D/SolidWorks/flange.het", "Match"))
    ]

sigsensGen :: String -> String -> IO (SigSens Env Sentence)
sigsensGen lb sp = do
  hlib <- getEnvDef "HETS_LIB" $ error "Missing HETS_LIB environment variable"
  let fp = if head lb == '/' then lb else hlib ++ "/" ++ lb
  res <- getSigSensComplete False myHetsOpts HasCASL fp sp
--  putStrLn "\n"
  return res { sigsensSignature = (sigsensSignature res) { globAnnos = sigsensGlobalAnnos res } }

siggy :: Int -> IO (SigSens Env Sentence)
siggy = uncurry sigsensGen . libFP

libFP :: Int -> (String, String)
libFP i = fromMaybe (error "libFP: no such spec") $ Prelude.lookup i testspecs

sigsens :: Int -> IO (Env, [Named Sentence])
sigsens i = do
  res <- siggy i
  return ( sigsensSignature res, sigsensNamedSentences res )

sig :: Int -> IO Env
sig = fmap fst . sigsens

-- Check if the order is broken or not!
sens :: Int -> IO [Named Sentence]
sens = fmap snd . sigsens

cmds :: Int -> IO [Sentence]
cmds = fmap (map sentence) . sens

-- time measurement, pendant of the time shell command
time :: MonadIO m => m a -> m a
time p = do
  t <- liftIO getCurrentTime
  res <- p
  t' <- liftIO getCurrentTime
  liftIO $ putStrLn "Time"
  liftIO $ putStrLn $ show $ diffUTCTime t' t
  liftIO $ putStrLn ""
  return res

times :: MonadIO m => m a -> m ()
times p = time p >> return ()


-- nice output
niceOut :: Env -> Doc -> IO ()
-- niceOut e = putStrLn . show . useGlobalAnnos (globAnnos e) . pretty
niceOut e x = do
  let ga = globAnnos e
--  putStrLn "Global Annotations:"
--  putStrLn $ show $ pretty $ ga
--  putStrLn "======================================================================"
  putStrLn $ show $ useGlobalAnnos ga x


prettyWithAnnos :: PrettyInEnv a => Env -> a -> Doc
prettyWithAnnos e = useGlobalAnnos (globAnnos e) . prettyInEnv e

prettyInSigs :: PrettyInEnv a => SigSens Env Sentence -> a -> Doc
prettyInSigs sigs = prettyWithAnnos (sigsensSignature sigs)

nice :: (MonadIO m, PrettyInEnv a) => SigSens Env Sentence -> m a -> m ()
nice sigs x = do
  y <- time x
  let e = sigsensSignature sigs
  liftIO $ niceOut e $ prettyInEnv e y

niceL :: (MonadIO m, PrettyInEnv a) => SigSens Env Sentence -> m [a] -> m ()
niceL sigs l = do
  l' <- time l
  let e = sigsensSignature sigs
  liftIO $ niceOut e $ prettyInEnvList e l'

prettyInEnvList :: PrettyInEnv a => Env -> [a] -> Doc
prettyInEnvList e = vsep . map (prettyInEnv e)


------------------------- New Testsuite -------------------------

typeFilter :: TypeScheme -> Bool
typeFilter = (flip elem ["SWExtrusion", "SWCut"]) . show . pretty

fromSigsNice :: (PrettyInEnv a) => SigSens Env Sentence -> String -> String
             -> (DefinitionStore -> DGNav -> String -> String -> IO a) -> IO ()
fromSigsNice sigs s1 s2 f = nice sigs $ fromSigs sigs s1 s2 f

fromSigsNiceL :: (PrettyInEnv a) => SigSens Env Sentence -> String -> String
             -> (DefinitionStore -> DGNav -> String -> String -> IO [a]) -> IO ()
fromSigsNiceL sigs s1 s2 f = niceL sigs $ fromSigs sigs s1 s2 f

fromSigs :: SigSens Env Sentence -> String -> String -> (DefinitionStore -> DGNav -> String -> String -> IO a) -> IO a
fromSigs sigs s1 s2 f =
  case prepareDefStore sigs s1 of
    Nothing ->  fail $ "Pattern spec " ++ s1 ++ " not found."
    Just (def, dgnav) -> f def dgnav s1 s2

prepareDefStore :: SigSens Env Sentence -> String -> Maybe (DefinitionStore, DGNav)
prepareDefStore sigs patN =
    let e = sigsensSignature sigs
        dgnav = mkDGNav sigs
        mGsyms = fromSearchResult (getActualParameterSpec patN) getLocalSyms dgnav
        f syms = (initialDefStore e $ Set.map gsymToSym syms, dgnav)
    in fmap f mGsyms

allMatches :: DefinitionStore -> DGNav
               -> String
               -> String
               -> IO [MatchResult]
allMatches def dgnav patN cN =
  let err = error "allMatches: no candidates found."
      g [] = return []
      g l = do
        (res, l') <- matchCandidates def l
        case res of
          Right mr -> fmap (mr :) $ g l'
          _ -> return []
  in g $ fromMaybe err $ getCandidates def dgnav typeFilter patN cN

findMatch :: (MatchResult -> Bool) -> DefinitionStore -> DGNav
               -> String
               -> String
               -> IO MatchResult
findMatch p def dgnav patN cN =
  let err = error "findMatch: no candidates found."
      err' = error "findMatch: no match satisfies predicate."
      g [] = err'
      g l = do
        (res, l') <- matchCandidates def l
        case res of
          Right mr -> if p mr then return mr else g l'
          _ -> err'
  in g $ fromMaybe err $ getCandidates def dgnav typeFilter patN cN


noConstraints :: MatchResult -> Bool
noConstraints (MatchResult (_, l)) = null l


testSpecMatchM :: SigSens Env Sentence
               -> String
               -> String
               -> IO ()
testSpecMatchM sigs patN cN =
  case prepareDefStore sigs patN of
    Nothing ->  fail $ "Pattern spec " ++ patN ++ " not found."
    Just (def, dgnav) -> do
      (res, l) <- matchSpecs def dgnav typeFilter 1 patN cN
      (res2, l') <- matchCandidates def l

      case res of
        Right mr -> 
            do
              putStrLn $ "Non tried elements: " ++ show (length l)
              nice sigs $ return mr
        Left s ->
            unless (null l) $ error "Not all tried!"
            putStrLn s

      putStrLn "------------------------------"

      case res2 of
        Right mr -> 
            do
              putStrLn $ "Non tried elements: " ++ show (length l')
              nice sigs $ return mr
        Left s ->
            unless (null l') $ error "Not all tried!"
            putStrLn s


------------------------- Template filler -------------------------


processTemplate :: (String -> a -> String) -> Map.Map String a -> String -> String
processTemplate f m s = unlines $ map g $ lines s where
    l = Map.toList m
    g ln = h ln l
    h ln [] = ln
    h ln ((k, v):l')
      | isInfixOf k ln = f k v
      | otherwise = h ln l'
    

------------------------- Shortcuts -------------------------

matchDesign :: String -- ^ The filename of the library containing the specs to match
            -> String -- ^ The specname importing the specs to match
            -> String -- ^ The pattern specname
            -> String -- ^ The concrete design specname
            -> IO ()
matchDesign lb sp patN cN = do
  sigs <- sigsensGen lb sp
  res <- fromSigs sigs patN cN (findMatch noConstraints)
  putStrLn $ show $ prettyInSigs sigs res
  return ()

getMatchMap :: String -- ^ The filename of the library containing the specs to match
            -> String -- ^ The specname importing the specs to match
            -> String -- ^ The pattern specname
            -> String -- ^ The concrete design specname
            -> IO (MatchResult, Map.Map String RealType)
getMatchMap lb sp patN cN = do
  sigs <- sigsensGen lb sp
  res <- fromSigs sigs patN cN (findMatch noConstraints)
  let (sbst, _) = getMatchResult res
      rcm = getRconsts (sigsensSignature sigs) sbst
  return (res, rcm)


