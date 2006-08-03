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
import System.Environment
import Comorphisms.CASL2PCFOL
import Comorphisms.CASL2SubCFOL
import Common.Result
import Maybe
import GUI.ShowGraph
-- import Common.DocUtils
-- import Debug.Trace

process :: FilePath -> IO (Maybe (LIB_NAME, LibEnv))
process file = do  
    mResult <- anaLib defaultHetcatsOpts file
    case mResult of
      Just (libName, gcMap) ->
          case Map.lookup libName gcMap of
            Just gc -> 
                do -- putStrLn ("orig: \n" ++ (show $ devGraph gc))
                   x  <-  compComorphism (Comorphism CASL2PCFOL) 
                                         (Comorphism CASL2SubCFOL)
                   gc' <- trans  x gc
                   -- putStrLn ("translated: \n" ++ (show $ devGraph gc'))
                   return $ Just (libName, Map.update (\_ -> Just gc') libName gcMap)
            _ -> do putStrLn "not found gc."
                    return mResult
      _ -> do putStrLn "analib error."
              return mResult

trans :: AnyComorphism -> GlobalContext -> IO GlobalContext
trans acm gc = do
    case dg_translation gc acm of
      Result diags' maybeGC ->
          do putStrLn ("diagnosis : \n" ++ (unlines $ map diagString $ filter (\x -> diagKind x /= Hint ) diags'))
             if hasErrors diags' then error "error(s) in translation."
              else do
               case maybeGC of
                Just gc' -> return gc'
                Nothing  -> do putStrLn "no translation" 
                               return gc
          
main :: IO()
main = do
  files <- getArgs
  if length files /= 1 then
      error "usage: TestDGTrans filename"
      else do let file = head files
              res <- process file
              showGraph file defaultHetcatsOpts res
  -- return ()

