module Main

where

import System.Environment
import qualified Common.Lib.Map as Map
import Static.AnalysisLibrary
import Static.DotGraph
import Static.DevGraph
import Driver.Options

process :: String -> IO()
process fname = do
  res <- anaLib defaultHetcatsOpts fname
  case res of
    Just(ln, lenv) -> case Map.lookup ln lenv of
        Nothing -> error "hetana: lookup"
        Just gctx -> do
           putStrLn ("Successfully analyzed.")
           putStrLn ("Writing development graph to "++fname++".dot")
           writeFile (fname++".dot") $ concat $ dot $ devGraph gctx
    Nothing -> error "hetana: anaFileOrGetEnv"

-- display *.dot file using "dotty"

main :: IO()
main = getArgs >>= mapM_ process
