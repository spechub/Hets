{-# OPTIONS_GHC -fno-warn-unused-imports -fno-warn-unused-binds #-}

import Syntax.AS_Library
import Static.AnalysisLibrary
import Static.GTheory
import Static.DevGraph
import Static.PrintDevGraph
import Driver.Options
import qualified Data.Map as Map
import Common.Doc
import Common.DocUtils
import Common.AS_Annotation
import System.Environment

-- CASL things

import Data.Maybe
import Data.List
import Common.Id as Id
import qualified Common.OrderedMap as OMap
import Common.AS_Annotation as Anno
import Common.Result
import Common.ResultT
import Common.ExtSign
import Logic.Coerce
import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.Sign
import Comorphisms.LogicGraph
import Static.AnalysisLibrary

-- DG things :)
import Proofs.Global
import Proofs.EdgeUtils
import Proofs.StatusUtils
import Data.Graph.Inductive.Graph
import Static.DGToSpec

myHetcatsOpts :: HetcatsOpts
myHetcatsOpts = defaultHetcatsOpts { libdir = "../Hets-lib" }

process :: FilePath -> IO (Maybe (LIB_NAME, LibEnv))
process = anaLib myHetcatsOpts

{- ln -s sample-ghci-script .ghci and call "make ghci" -}

-- sample code
getDevGraph :: FilePath -> IO DGraph
getDevGraph fname = do
  res <- process fname
  case res of
    Nothing -> error "getDevGraph: process"
    Just (ln, lenv) -> case Map.lookup ln lenv of
        Nothing -> error "getDevGraph: lookup"
        Just dg -> return dg

main :: IO()
main = do
  files <- getArgs
  mapM_ process files
  return ()


{- Test functions for CASL signature -}

proceed :: FilePath -> ResultT IO (LIB_NAME, LibEnv)
proceed fname = do
  anaSourceFile logicGraph myHetcatsOpts emptyLibEnv fname

-- read in a CASL file and return the basic theory
getCASLSigSens ::    String -- filename
                  -> String  -- name of spec
                  -> IO (CASLSign,[(String, CASLFORMULA)])
getCASLSigSens fname sp = do
  Result _ res <- runResultT $ proceed fname
  case res of
    Just (ln,lenv) ->
     let dg = lookupDGraph ln lenv
         SpecEntry (ExtGenSig _ _ _ (NodeSig node _)) =
            case Map.lookup (Id.mkSimpleId sp) $ globalEnv dg of
              Just x -> x
              _ -> error ("Specification "++sp++" not found")
     in
      case match node (dgBody dg) of
        (Just ctx,_) ->
          case dgn_theory $ lab' ctx of
           G_theory { gTheoryLogic = lid
                    , gTheorySign = gSig
                    , gTheorySens = gSens } ->
            case (coerceSign lid CASL "" $ gSig,
                 coerceThSens lid CASL "" $ gSens) of
             (Just sig,Just sens) ->
                return (plainSign sig,
                        map (\(x,y) -> (x,Anno.sentence y)) $ OMap.toList sens)
             _ -> error "Not a CASL sig"
        _ -> error "Node 1 no in development graph"
    Nothing -> error "Error occured"


{- myTest for globDecomp(or more possiblely for removeContraryChanges
from Proofs/StatusUtils.hs -}

{- try to print the DGChanges list before and after executing
removeContraryChanges, in order to see what exactly is going on -}

myTest :: IO()
myTest = do
    res <- process "../Hets-lib/Basic/RelationsAndOrders.casl"
    -- not ok with "RelationsAndOrders.casl " :(
    case res of
       Nothing -> error "myTest"
       Just (ln, lenv) -> do
{-       (edges2, dgchanges2) <- myGlobal ln 2 lenv
         putStrLn $ show dgchanges
-- print the DGChanges before execusion
         putStrLn $ "!!!!!The DGChanges before excecuting of " ++
                      "removeContraryChanges by the third excecuting of " ++
                      "GlobalDecomposition!!!!!"
         putStrLn $ show $ myPrintShow dgchanges2
         putStrLn $ "!!!!!the DGChanges afterwards by the third excecuting"
                    ++ " of GlobalDecomposition!!!!!"
         putStrLn $ show $ myPrintShow $
-- removeContraryChanges dgchanges2
         putStrLn $ show $ myPrintEdges edges2
-}
         (edges3, dgchanges3) <- myGlobal ln 3 lenv
         putStrLn $ "The global thm Edges before executing globDecomp for " ++
                    "the fourth time"
         putStrLn $ show $ myPrintEdges edges3
{-       putStrLn $ "!!!!!The DGChanges before excecuting of " ++
                    "removeContraryChanges by the fouth excecuting of " ++
                    "GlobalDecomposition!!!!!"
         putStrLn $ show $ myPrintShow dgchanges3
-}
         putStrLn $ "!!!!!the DGChanges by the fouth excecuting of " ++
                    "GlobalDecomposition: !!!!!"
         putStrLn $ show $ myPrintDGChanges dgchanges3
         putStrLn $ show $ myPrintDGChanges $ removeContraryChanges dgchanges3
{-       putStrLn $ show (removeContraryChanges dgchanges)
-- print after...
         putStrLn $ show $ countD $ removeContraryChanges dgchanges
         dgchanges4<- myGlobal ln 4 lenv
         putStrLn "aaa"
-}

myPrintEdges :: [LEdge DGLinkLab] -> [String]
myPrintEdges = map showLEdge

showDGChange :: DGChange -> String
showDGChange c = showDoc c ""

myPrintDGChanges :: [DGChange] -> [String]
myPrintDGChanges = map showDGChange

countD :: [DGChange] -> Int
countD = length . filter (isPrefixOf "delete edge" . showDGChange)

-- my simulated execusion of globDecomp
myGlobal :: LIB_NAME -> Int -> LibEnv -> IO ([LEdge DGLinkLab], [DGChange])
myGlobal ln n lenv =
    let newLenv = executeGlobalDecompByNTimes n ln lenv
        -- try to do n times globDecomp
        dgraph = lookupDGraph ln newLenv
        globalThmEdges = filter (liftE isUnprovenGlobalThm) (labEdgesDG dgraph)
        (_, newHistoryElems) = mapAccumL globDecompAux dgraph globalThmEdges
        defEdgesToSource = myGoingIntoGTE dgraph globalThmEdges []
    in do putStrLn "all the edges going into global Thm Edges"
          putStrLn $ show defEdgesToSource
          return (globalThmEdges , concatMap snd newHistoryElems)
            -- get the DGChanges by the fourth time executing globDecomp

myGoingIntoGTE :: DGraph -> [LEdge DGLinkLab] -> [String]->[String]
myGoingIntoGTE _ [] res = res
myGoingIntoGTE dgraph ((source, _ , _) : ys) res =
    let defEdgesToSource = [e | e@(_, t, l) <- labEdgesDG dgraph,
                            isDefEdge (dgl_type l), t == source]

    in  myGoingIntoGTE dgraph ys (res++(myPrintEdges defEdgesToSource))

-- execute globDecomp by n times :)
executeGlobalDecompByNTimes :: Int -> LIB_NAME -> LibEnv -> LibEnv
executeGlobalDecompByNTimes n ln lenv =
    if n<0 then error "excecuteGlobalDecompByNTimes"
    else if n==0 then lenv
         else executeGlobalDecompByNTimes (n-1) ln $ globDecomp ln lenv
