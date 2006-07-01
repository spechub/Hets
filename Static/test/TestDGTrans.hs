{- |
Module      :  $Header$
Copyright   :  Heng Jiang, Uni Bremen 2004-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Central data structure for development graphs.
   Follows Sect. IV:4.2 of the CASL Reference Manual.
-}

module Static.Test.TestDGTrans where

import Static.DGTranslation
import Logic.Logic
import Logic.Coerce
import Logic.Comorphism
import Logic.Grothendieck
import Logic.Prover

import Syntax.AS_Library
import Static.AnalysisLibrary
import Static.DevGraph
import Static.PrintDevGraph
import Driver.Options
import qualified Common.Lib.Map as Map
import Common.Doc
import System.Environment
import Comorphisms.PCFOL2CFOL
import Common.Result
import Maybe


process :: FilePath -> IO (Maybe (LIB_NAME, LibEnv))
process = anaLib defaultHetcatsOpts

process2 :: FilePath -> IO (Maybe (LIB_NAME, LibEnv))
process2 = do  
    mResult <-anaLib defaultHetcatsOpts
    case mResult of
      Just (libName, gcMap) ->
          case Map.lookup libName gcMap of
            Just gc -> 
                do putStrLn ("find: " ++ 
                             (show $ libName) ++ " in " ++ 
                             (show mResult))
                   putStrLn $ show gc
                   gc' <- trans_PCFOL2CFOL gc
                   putStrLn $ show $ gc'
                   if gc == gc' then
                       putStrLn "equals!"
                     else putStrLn "difference!"
                   return mResult
            _ -> do putStrLn "not found gc."
                    return mResult
      _ -> do putStrLn "nichts"
              return mResult


printLibEnv :: LibEnv -> Doc
printLibEnv le = vsep $ map (printLibrary le) $ Map.toList le

{- Call this function as follows
make
make ghci
:l Test.hs
Just (_, lenv) <- process "../CASL-lib/List.casl"
printLibEnv lenv
-}


trans_PCFOL2CFOL :: GlobalContext -> IO GlobalContext
trans_PCFOL2CFOL gc = do
    case dg_translation gc (Comorphism PCFOL2CFOL) of
      Result diags maybeGC ->
          do putStrLn $ show diags
             case maybeGC of
               Just gc' -> return gc'
               Nothing  -> return gc


main :: IO()
main = do
  files <- getArgs
  mapM_ process files
  return ()