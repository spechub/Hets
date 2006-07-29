{- |
Module      :  $Header$
Copyright   :  Heng Jiang, Uni Bremen 2004-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Test Logic translation for development graphs.
   Follows Sect. IV:4.2 of the CASL Reference Manual.
-}

module Main where -- Static.Test.TestDGTrans where

import Static.DGTranslation
-- import Logic.Logic
-- import Logic.Coerce
import Logic.Comorphism
import Logic.Grothendieck
-- import Logic.Prover

import Syntax.AS_Library
import Static.AnalysisLibrary
import Static.DevGraph
-- import Static.PrintDevGraph
import Driver.Options
import qualified Common.Lib.Map as Map
-- import Common.Doc
import System.Environment
-- import Comorphisms.PCFOL2CFOL
import Comorphisms.CASL2PCFOL
import Comorphisms.CASL2SubCFOL
import Common.Result
import Maybe
import GUI.ShowGraph
import Common.Lib.Graph
-- import Common.DocUtils
import Debug.Trace

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
                   return $ Just (libName, Map.update (\_ -> Just (trace (show (devGraph gc') ++ "\n\n") gc')) libName gcMap)
            _ -> do putStrLn "not found gc."
                    return mResult
      _ -> do putStrLn "analib error."
              return mResult

trans :: AnyComorphism -> GlobalContext -> IO GlobalContext
trans acm gc = do
    case dg_translation gc acm of
      Result diags' maybeGC ->
          do putStrLn ("diagnosis : \n" ++ (show $ filter isErrorDiag diags'))
             if hasErrors diags' then error "error(s) in translation."
              else do
               case maybeGC of
                Just gc' -> if not $ isLessSubLogic acm $ devGraph gc'
                             then do putStrLn ("anyplace is not less" ++ 
                                               "than Comorphism.")
                                     return gc'
                             else return gc'
                Nothing  -> do putStrLn "no translation" 
                               return gc

isLessSubLogic :: AnyComorphism -> DGraph -> Bool
isLessSubLogic acm dg =
    all checkAllLess (Map.elems $ toMap dg)

  where checkAllLess (inlinks, node, outlinks) =
            if lessSublogicComor (sublogicOfTh $ dgn_theory node) acm
               then all checkEdgeLess (inlinks ++ outlinks)
               else error ((show $ dgn_name node) ++ " not less than" 
                           ++ (show acm)) -- False

        checkEdgeLess (edge, _) =
            case dgl_morphism edge of
              gm@(GMorphism cid _ _) ->
                  if isHomogeneous gm then
                      if lessSublogicComor (G_sublogics 
                            (sourceLogic cid) (sourceSublogic cid)) acm
                         then True
                         else -- error ("near of node " ++ (show n) ++ " has a edge not less than " ++ (show acm)) 
                              False
                     else True
            
main :: IO()
main = do
  files <- getArgs
  if length files /= 1 then
      error "usage: TestDGTrans filename"
      else do let file = head files
              res <- process file
              showGraph file defaultHetcatsOpts res
  -- return ()

