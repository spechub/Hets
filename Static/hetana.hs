module Main

where

import System.Environment
import qualified Common.Lib.Map as Map
import Static.AnalysisLibrary
import Static.DotGraph
import Driver.Options

process :: String -> IO()
process fname = do
  res <- anaLib defaultHetcatsOpts fname
  case res of
    Just(ln,lenv) -> case Map.lookup ln lenv of
        Nothing -> error "hetana: lookup"
        Just (_,_,dg) -> do 
           putStrLn ("Successfully analyzed.")
           putStrLn ("Writing development graph to "++fname++".dot")
           writeFile (fname++".dot") $ concat $ dot dg
    Nothing -> error "hetana: anaFileOrGetEnv"

-- display *.dot file using "dotty"

main :: IO()
main = getArgs >>= mapM_ process



