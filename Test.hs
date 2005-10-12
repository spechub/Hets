
import Syntax.AS_Library
import Static.AnalysisLibrary
import Static.DevGraph
import Static.PrintDevGraph
import Driver.Options
import qualified Common.Lib.Map as Map
import Common.Lib.Pretty

import System.Environment

process :: FilePath -> IO (Maybe (LIB_NAME, LibEnv))
process = anaLib defaultHetcatsOpts

printLibEnv :: LibEnv -> Doc
printLibEnv le = vcat $ map (printLibrary le) $ Map.toList le

{- Call this function as follows
make
make ghci
:l Test.hs
Just (_, lenv) <- process "../CASL-lib/List.casl"
printLibEnv lenv
-}

-- sample code
getDevGraph :: FilePath -> IO DGraph
getDevGraph fname = do
  res <- process fname
  case res of
    Nothing -> error "getDevGraph: process"
    Just (ln, lenv) -> case Map.lookup ln lenv of
        Nothing -> error "getDevGraph: lookup"
        Just (_,_,dg) -> return dg

main :: IO()
main = do
  files <- getArgs
  mapM_ process files
  return ()

