{-# OPTIONS_GHC -fno-warn-unused-imports -fno-warn-unused-binds #-}

{- |
Module      :  $Header$
Description :  ghci test file
Copyright   :  (c)  C. Maeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  non-portable (import Logic)

load after calling make ghci
-}

module Main where

import Syntax.AS_Library
import Static.AnalysisLibrary
import Static.GTheory
import Static.DevGraph
import Static.PrintDevGraph
import Static.History
import Static.ComputeTheory

import Driver.Options
import Driver.AnaLib

import qualified Common.OrderedMap as OMap
import Common.GlobalAnnotations
import Common.AS_Annotation as Anno
import Common.Result
import Common.ResultT
import Common.LibName
import Common.Id as Id
import Common.ExtSign
import Common.Doc
import Common.DocUtils

import System.Environment
import Data.Graph.Inductive.Graph
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe
import Data.List

-- Logic things
import Logic.Coerce
import Logic.Logic

-- CASL things
import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.Sign
import Comorphisms.LogicGraph

-- DG things :)
import Proofs.Global
import Proofs.EdgeUtils
import Proofs.StatusUtils
import Proofs.Automatic

import Static.SpecLoader

myHetcatsOpts :: HetcatsOpts
myHetcatsOpts = defaultHetcatsOpts { libdirs = ["../Hets-lib"] }

process :: FilePath -> IO (Maybe (LibName, LibEnv))
process = anaLib myHetcatsOpts

-- ln -s sample-ghci-script .ghci and call "make ghci"

-- sample code
getDevGraph :: FilePath -> IO DGraph
getDevGraph fname = do
  res <- process fname
  case res of
    Nothing -> error "getDevGraph: process"
    Just (ln, lenv) -> case Map.lookup ln lenv of
        Nothing -> error "getDevGraph: lookup"
        Just dg -> return dg

main :: IO ()
main = do
  files <- getArgs
  mapM_ process files
  return ()



proceed :: FilePath -> ResultT IO (LibName, LibEnv)
proceed = proceed' myHetcatsOpts



-- Test functions for CASL signature

-- read in a CASL file and return the basic theory
getCASLSigSens :: String -- filename
                  -> String  -- name of spec
                  -> IO (CASLSign, [(String, CASLFORMULA)])
getCASLSigSens fname sp = do
  res <- getSigSens myHetcatsOpts CASL fname sp
  let f z = (senAttr z, sentence z)
  return (sigsensSignature res, map f $ sigsensNamedSentences res)


{- myTest for globDecomp(or more possiblely for removeContraryChanges
from Proofs/StatusUtils.hs -}

{- try to print the DGChanges list before and after executing
removeContraryChanges, in order to see what exactly is going on -}

myTest :: IO ()
myTest = do
    res <- process "../Hets-lib/Basic/RelationsAndOrders.casl"
    -- not ok with "RelationsAndOrders.casl " :(
    case res of
       Nothing -> error "myTest"
       Just (ln, lenv) -> do
{-
         (edges2, dgchanges2) <- myGlobal ln 2 lenv
         print dgchanges
         -- print the DGChanges before execusion
         putStrLn $ "!!!!!The DGChanges before excecuting of " ++
                      "removeContraryChanges by the third excecuting of " ++
                      "GlobalDecomposition!!!!!"
         print $ myPrintShow dgchanges2
         putStrLn $ "!!!!!the DGChanges afterwards by the third excecuting"
                    ++ " of GlobalDecomposition!!!!!"
         print $ myPrintShow $
         -- removeContraryChanges dgchanges2
         print $ myPrintEdges edges2
-}
         (edges3, dgchanges3) <- myGlobal ln 3 lenv
         putStrLn $ "The global thm Edges before executing globDecomp for " ++
                    "the fourth time"
         print $ myPrintEdges edges3
{-
         putStrLn $ "!!!!!The DGChanges before excecuting of " ++
                    "removeContraryChanges by the fouth excecuting of " ++
                    "GlobalDecomposition!!!!!"
         print $ myPrintShow dgchanges3
-}
         putStrLn $ "!!!!!the DGChanges by the fouth excecuting of " ++
                    "GlobalDecomposition: !!!!!"
         print $ myPrintDGChanges dgchanges3
         print $ myPrintDGChanges $ removeContraryChanges dgchanges3
{-
         print (removeContraryChanges dgchanges)
         -- print after...
         print $ countD $ removeContraryChanges dgchanges
         dgchanges4<- myGlobal ln 4 lenv
         putStrLn "aaa"
-}

myPrintEdges :: [LEdge DGLinkLab] -> [String]
myPrintEdges = map showLEdge

showDGChange :: DGChange -> String
showDGChange c = showDoc c ""

myPrintDGChanges :: [DGChange] -> [String]
myPrintDGChanges = map showDGChange

countD :: [DGChange] -> Int
countD = length . filter (isPrefixOf "delete edge" . showDGChange)

-- my simulated execusion of globDecomp
myGlobal :: LibName -> Int -> LibEnv -> IO ([LEdge DGLinkLab], [DGChange])
myGlobal ln n lenv = do
    let newLenv = executeGlobalDecompByNTimes n ln lenv
        -- try to do n times globDecomp
        dgraph = lookupDGraph ln newLenv
        globalThmEdges = filter (liftE isUnprovenGlobalThm) (labEdgesDG dgraph)
        ngraph = foldl globDecompAux dgraph globalThmEdges
        defEdgesToSource = myGoingIntoGTE dgraph globalThmEdges []
    putStrLn "all the edges going into global Thm Edges"
    print defEdgesToSource
    return (globalThmEdges,
             flatHistory $ snd $ splitHistory dgraph ngraph)
            -- get the DGChanges by executing globDecomp

myGoingIntoGTE :: DGraph -> [LEdge DGLinkLab] -> [String] -> [String]
myGoingIntoGTE _ [] res = res
myGoingIntoGTE dgraph ((source, _ , _) : ys) res =
    let defEdgesToSource = [e | e@(_, t, l) <- labEdgesDG dgraph,
                            isDefEdge (dgl_type l), t == source]

    in myGoingIntoGTE dgraph ys $ res ++ myPrintEdges defEdgesToSource

-- execute globDecomp by n times :)
executeGlobalDecompByNTimes :: Int -> LibName -> LibEnv -> LibEnv
executeGlobalDecompByNTimes n ln lenv = case compare n 0 of
  LT -> error "excecuteGlobalDecompByNTimes"
  EQ -> lenv
  GT -> executeGlobalDecompByNTimes (n - 1) ln $ globDecomp ln lenv
