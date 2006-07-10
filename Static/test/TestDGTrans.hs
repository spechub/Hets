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
-- import Logic.Comorphism
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


instance Eq GlobalContext where
    gc1 == gc2 = 
        (show $ devGraph gc1) == (show $ devGraph gc2)

process :: FilePath -> IO (Maybe (LIB_NAME, LibEnv))
process = anaLib defaultHetcatsOpts

process2 :: FilePath -> IO (Maybe (LIB_NAME, LibEnv))
process2 file = do  
    mResult <- anaLib defaultHetcatsOpts file
    case mResult of
      Just (libName, gcMap) ->
          case Map.lookup libName gcMap of
            Just gc -> 
                do putStrLn ("orig: \n" ++ (show $ devGraph gc))
                   gc' <- trans_PCFOL2CFOL gc
                   putStrLn ("translated: \n" ++ (show $ devGraph gc'))
                   if gc == gc' then
                       putStrLn "equals!"
                     else putStrLn "difference!"
                   return mResult
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


trans_PCFOL2CFOL :: GlobalContext -> IO GlobalContext
trans_PCFOL2CFOL gc = do
    case dg_translation gc (Comorphism PCFOL2CFOL) of
      Result diags' maybeGC ->
          do putStrLn ("diagnosis : \n" ++ (show diags'))
             case maybeGC of
               Just gc' -> return gc'
               Nothing  -> return gc


main :: IO()
main = do
  file <- getArgs
  mapM_ process2 file
  return ()
