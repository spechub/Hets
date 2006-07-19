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
import Comorphisms.PCFOL2CFOL
import Common.Result
import Maybe
import GUI.ShowGraph
import Common.Lib.Graph


process :: FilePath -> IO (Maybe (LIB_NAME, LibEnv))
process = anaLib defaultHetcatsOpts

process2 :: FilePath -> IO (Maybe (LIB_NAME, LibEnv))
process2 file = do  
    mResult <- anaLib defaultHetcatsOpts file
    case mResult of
      Just (libName, gcMap) ->
          case Map.lookup libName gcMap of
            Just gc -> 
                do -- putStrLn ("orig: \n" ++ (show $ devGraph gc))
{-                x  <-  compComorphism (Comorphism CASL2PCFOL) 
                                     (Comorphism CASL2SubCFOL)-}
                   gc' <- trans (Comorphism PCFOL2CFOL) gc
                   -- putStrLn ("translated: \n" ++ (show $ devGraph gc'))
                   return $ Just (libName, Map.update (\_ -> Just gc') libName gcMap)
            _ -> do putStrLn "not found gc."
                    return mResult
      _ -> do putStrLn "nichts"
              return mResult

{- Call this function as follows
make
make ghci
:l Test.hs
Just (_, lenv) <- process "../CASL-lib/List.casl"
printLibEnv lenv
-}


trans :: AnyComorphism -> GlobalContext -> IO GlobalContext
trans acm gc = do
    case dg_translation gc acm of
      Result diags' maybeGC ->
          do putStrLn ("diagnosis : \n" ++ (show diags'))
             case maybeGC of
               Just gc' -> if not $ isLessSubLogic acm $ devGraph gc'
                             then do putStrLn ("anyplace is not less" ++ 
                                               "than Comorphism.")
                                     return gc'
                             else return gc'
               Nothing  -> do putStrLn "no result from translation" 
                              return gc

isLessSubLogic :: AnyComorphism -> DGraph -> Bool
isLessSubLogic acm dg =
    all checkAllLess (Map.elems $ toMap dg)

  where checkAllLess (inlinks, node, outlinks) =
            if lessSublogicComor (sublogicOfTh $ dgn_theory node) acm
               then all checkEdgeLess (inlinks ++ outlinks)
               else error ((show $ dgn_name node) ++ " not less than" 
                           ++ (show acm)) -- False

        checkEdgeLess (edge, n) =
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
              res <- process2 file
              showGraph file defaultHetcatsOpts res
  -- return ()

