import Syntax.AS_Library
import Static.AnalysisLibrary
import Static.DevGraph
import Static.PrintDevGraph
import Driver.Options
import qualified Common.Lib.Map as Map
import Common.Doc
import System.Environment

-- my things :)
import Proofs.Global
import Proofs.EdgeUtils
import Proofs.StatusUtils
import Data.Graph.Inductive.Graph
import GUI.ConvertDevToAbstractGraph
import Static.DGToSpec

process :: FilePath -> IO (Maybe (LIB_NAME, LibEnv))
process = anaLib defaultHetcatsOpts

printLibEnv :: LibEnv -> Doc
printLibEnv le = vsep $ map (printLibrary le) $ Map.toList le


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
        Just gctx -> return $ devGraph gctx

main :: IO()
main = do
  files <- getArgs
  mapM_ process files
  return ()


-- myTest for globDecomp(or more possiblely for removeContraryChanges from Proofs/StatusUtils.hs)

-- try to print the DGChanges list before and after executing
-- removeContraryChanges, in order to see what exactly is going 
-- here... 
myTest :: IO()
myTest = do
    res<-process "../CASL-lib/Basic/RelationsAndOrders.casl" -- not ok with "RelationsAndOrders.casl " :(
    case res of
       Nothing -> error "myTest"
       Just (ln, lenv) -> do --(edges2, dgchanges2) <- myGlobal ln 2 lenv
			     --putStrLn $ show dgchanges  -- print the DGChanges before execusion 
			     --putStrLn "!!!!!The DGChanges before excecuting of removeContraryChanges by the third excecuting of GlobalDecomposition!!!!!"
			     --putStrLn $ show $ myPrintShow dgchanges2
			     --putStrLn "!!!!!the DGChanges afterwards by the third excecuting of GlobalDecomposition!!!!!"
			     --putStrLn $ show $ myPrintShow $
-- removeContraryChanges dgchanges2
			     --putStrLn $ show $ myPrintEdges edges2
			     (edges3, dgchanges3) <- myGlobal ln 3 lenv
			     putStrLn "The global thm Edges before executing globDecomp for the fourth time"
			     putStrLn $ show $ myPrintEdges edges3
			     --putStrLn "!!!!!The DGChanges before excecuting of removeContraryChanges by the fouth excecuting of GlobalDecomposition!!!!!"
			     --putStrLn $ show $ myPrintShow dgchanges3
			     putStrLn "!!!!!the DGChanges by the fouth excecuting of GlobalDecomposition: !!!!!"
			     --putStrLn $ show $ myPrintDGChanges dgchanges3
			     putStrLn $ show $ myPrintDGChanges dgchanges3
			     putStrLn $ show $ myPrintDGChanges $ removeContraryChanges dgchanges3
			     --putStrLn $ show (removeContraryChanges dgchanges) -- print after...
			     --llllll <- countD (removeContraryChanges dgchanges) 0
			     --putStrLn $ show llllll
			     --dgchanges4<- myGlobal ln 4 lenv
			     --putStrLn "aaa"

myPrintEdges :: [LEdge DGLinkLab] -> [String]
myPrintEdges edges = [edgesAux edge|edge<-edges]

edgesAux :: LEdge DGLinkLab -> String
edgesAux edge@(s, t, l) = ((show source) ++ "->" ++ (show target) ++ " with type" ++ (show $ dgl_type l)) 
	 where source = getSourceNode edge
	       target = getTargetNode edge

myPrintDGChanges :: [DGChange] -> [String]
myPrintDGChanges dgs = [show dg++" "++ myPrintAux dg|dg<-dgs]

myPrintAux :: DGChange -> String
myPrintAux (DeleteEdge (_, _, dglink)) = getDGLinkType dglink
myPrintAux (InsertEdge (_, _, dglink)) = getDGLinkType dglink
myPrintAux _ = "Node"

countD :: [DGChange] -> Int -> IO Int
countD [] n = return n
countD (x:xs) n = if show x == "DeleteEdge 3->15" then countD xs (n+1) 
						  else countD xs n

-- my simulated execusion of globDecomp
myGlobal :: LIB_NAME -> Int -> LibEnv -> IO ([LEdge DGLinkLab], [DGChange])
myGlobal ln n lenv = 
    let newLenv = executeGlobalDecompByNTimes n ln lenv -- try to do n times globDecomp
	dgraph = lookupDGraph ln newLenv
	globalThmEdges = filter isUnprovenGlobalThm (labEdges dgraph)
	(newDGraph, newHistoryElem) = globDecompAux dgraph globalThmEdges ([], [])
	defEdgesToSource = myGoingIntoGTE dgraph globalThmEdges []
    in --do putStrLn $ show (labEdges dgraph)
       do putStrLn "all the edges going into global Thm Edges"
	  putStrLn $ show defEdgesToSource
          return (globalThmEdges , snd newHistoryElem) -- get the DGChanges by the fourth time executing globDecomp

myGoingIntoGTE :: DGraph -> [LEdge DGLinkLab] -> [String]->[String]
myGoingIntoGTE dgraph [] res = res
myGoingIntoGTE dgraph (gte:ys) res = 
    let source = getSourceNode gte
        defEdgesToSource = [e | e <- labEdges dgraph, isDefEdge e && (getTargetNode e)==source]
	
    in  myGoingIntoGTE dgraph ys (res++(myPrintEdges defEdgesToSource)) 

-- execute globDecomp by n times :)
executeGlobalDecompByNTimes :: Int -> LIB_NAME -> LibEnv -> LibEnv
executeGlobalDecompByNTimes n ln lenv = 
    if n<0 then error "excecuteGlobalDecompByNTimes"
    else if n==0 then lenv
	 else executeGlobalDecompByNTimes (n-1) ln $ globDecomp ln lenv



