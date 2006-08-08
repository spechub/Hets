{- |
Module      :  $Header$
Copyright   :  Heng Jiang, Uni Bremen 2004-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Test Logic translation for development graphs.
   Follows Sect. IV:4.2 of the CASL Reference Manual.
-}

module Main where -- Static.Test.TestDGTrans where

import Static.DGTranslation
import Logic.Grothendieck

import Syntax.AS_Library
import Static.AnalysisLibrary
import Static.DevGraph
import Driver.Options
import qualified Common.Lib.Map as Map
import qualified List as List
import System.Environment
import Comorphisms.CASL2PCFOL
import Comorphisms.CASL2SubCFOL
import Common.Result
import Maybe
import GUI.ShowGraph
-- import Common.DocUtils
-- import Debug.Trace

process :: HetcatsOpts -> FilePath -> IO (Maybe (LIB_NAME, LibEnv))
process opts file = do  
    mResult <- anaLib opts file
    
    case mResult of
      Just (libName, gcMap) ->
          do 
            newGc <- updateGc (Map.keys gcMap) gcMap
            return $ Just (libName, newGc)
      _ -> do putStrLn "analib error."
              return mResult

   where updateGc :: [LIB_NAME] -> LibEnv -> IO LibEnv
         updateGc [] le = return le
         updateGc (k1:kr) le = do
             let gc = lookupGlobalContext k1 le
             x  <-  compComorphism (Comorphism CASL2PCFOL) 
                                   (Comorphism CASL2SubCFOL)
             gc' <- trans x gc
             updateGc kr (Map.update (\_ -> Just gc') k1 le)

trans :: AnyComorphism -> GlobalContext -> IO GlobalContext
trans acm gc = do
    case dg_translation gc acm of
      Result diags' maybeGC ->
          do putStrLn ("diagnosis : \n" ++ 
                       (unlines $ map diagWithoutTail $ List.nub diags'))
             if hasErrors diags' then error "error(s) in translation."
              else do
               case maybeGC of
                Just gc' -> return gc'
                Nothing  -> do putStrLn "no translation" 
                               return gc
     where diagWithoutTail d = let s = diagString d
                                   len = length s
                               in  take (len-2) s
          
main :: IO()
main = do
  opts <- getArgs >>= hetcatsOpts
  files <- getArgs
  if length files /= 1 then
      error "usage: TestDGTrans filename"
      else do let file = head files
              res <- process opts file
              showGraph file defaultHetcatsOpts res
  -- return ()

