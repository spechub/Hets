{- |
Module      :  $Header$
Description :  create a slightly faked dependency graph of the hets directories
Copyright   :  (c) jianchun wang and Uni Bremen 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

in order to generate the graph, hets needs to be created with
-ddump-minimal-imports first. Start the GUI\/displayDependencyGraph
binary that reads in the .imports files in the top-level directory and
save the graph as postscript possibly after moving some edges and
nodes. Suitably convert the postscript file to a .png file and upload
it.

If the graph contains cycles exclude suitable modules in 'exclude'.

* File, Print..., Page Size A3, Fit to Page, Send to: File

* convert -rotate 90 graph.ps graph.png


-}

module Main where

-- for graph display
import UDrawGraph.Graph
import Graphs.GraphDisp
import Graphs.GraphConfigure

-- for windows display
import HTk.Toolkit.TextDisplay
import HTk.Kernel.Configuration (size)
import Events.Events (sync)
import Events.Destructible (destroy, destroyed)
import qualified HTk.Toplevel.HTk as HTk

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Common.Lib.Rel as Rel

import System.Directory
import Data.List

main :: IO ()
main = do
    fs <- getDirectoryContents "."
    let suf = ".imports"
        fn = filter (isSuffixOf suf) fs
        ffn = map ( \ s -> take (length s - length suf) s) fn
        ffnn = filter exclude $ filter (elem '.') ffn
        fln = map (fst . break (== '.'))  ffnn
        fln' = nub fln
    lfs <- mapM (readFile . (++ suf)) ffnn
    let ss = map (filter (isPrefixOf "import") . lines) lfs
        sss = getContent6 ss
        ssss' = map (filter exclude) sss
        ssss = map (map $ fst . break (== '.')) ssss'
        sss' = map nub ssss
        graphParms = GraphTitle "Dependency Graph" $$
                        OptimiseLayout True $$
                        AllowClose (return True) $$
                        emptyGraphParms
    wishInst <- HTk.initHTk [HTk.withdrawMainWin]
    depG <- newGraph daVinciSort graphParms
    let flln = nub $ fln' ++ concat sss'
        subNodeMenu = LocalMenu (Menu (Just "Info") [
                      Button "Contents" (\lg -> createTextDisplay
                      ("Contents of " ++ lg)
                       (showCon lg) [size(80,25)])])
        showCon lg = unlines (filter (isPrefixOf (lg++".")) ffnn)
        subNodeTypeParms =
                         subNodeMenu $$$
                         Ellipse $$$
                         ValueTitle return $$$
                         Color "yellow" $$$
                         emptyNodeTypeParms
    subNodeType <- newNodeType depG subNodeTypeParms
    subNodeList <- mapM (newNode depG subNodeType) flln
    let slAndNodes = Map.fromList $ zip flln subNodeList
        lookup' g_sl = Map.findWithDefault
                              (error "lookup': node not found")
                              g_sl slAndNodes
        subArcMenu = LocalMenu( Menu Nothing [])
        subArcTypeParms = subArcMenu $$$
                          ValueTitle id $$$
                            Color "green" $$$
                          emptyArcTypeParms
    subArcType <- newArcType depG subArcTypeParms
    let insertSubArc (node1, node2) =
                           newArc depG subArcType (return "")
                                  (lookup' node1)
                                  (lookup' node2)
    mapM_ insertSubArc $
                     Rel.toList $ Rel.intransKernel $ Rel.transClosure $
                        Rel.fromList
                     $ isIn3 $ concat $ zipWith getContent2 fln sss'
    redraw depG
    sync(destroyed depG)
    destroy wishInst
    HTk.finishHTk

exclude :: String -> Bool
exclude s = not
    $ isPrefixOf "ATC." s || isPrefixOf ".ATC_" (dropWhile (/= '.') s)
    || Set.member s (Set.fromList
    [ "Isabelle.CreateTheories"
    , "CspCASLProver.Utils", "CspCASLProver.IsabelleUtils"
    , "CspCASLProver.TransProcesses", "CspCASLProver.CspCASLProver"
    , "CASL.QuickCheck"
    , "OWL.StructureAnalysis", "OWL.OWLAnalysis"
    , "OWL.ProvePellet", "OWL.ProveFact"
    , "Proofs.InferBasic", "Proofs.BatchProcessing"
    , "Comorphisms.GetPreludeLib"
    , "Maude.Maude2DG", "Maude.PreComorphism"
    , "Haskell.Haskell2DG", "Haskell.CreateModules"
    , "Comorphisms.KnownProvers", "Comorphisms.LogicGraph"
    , "Interfaces.GenericATPState"
    , "GUI.Utils", "GUI.Taxonomy"
    , "Driver.Options" -- Static
    , "GUI.GenericATP", "SoftFOL.CreateDFGDoc"
    , "SoftFOL.MathServMapping", "SoftFOL.ProveMathServ"
    , "SoftFOL.ProveDarwin", "SoftFOL.ProveSPASS"
    , "SoftFOL.ProveVampire", "SoftFOL.ProverState"
    , "Taxonomy.MMiSSOntologyGraph"
    , "Propositional.Prop2CNF", "Propositional.Prop2CASLHelpers"
    , "Propositional.Prove"
    , "Modifications.ModalEmbedding"
    , "Static.AnalysisLibrary", "Static.WACocone"
    , "OMDoc.OMDocDefs", "OMDoc.OMDocOutput", "OMDoc.DataTypes"
    , "OMDoc.Export", "OMDoc.Sentences"
    , "OMDoc.OMDocInput", "OMDoc.HetsDefs", "Debug.Trace"
    ])

getContent2 :: String -> [String] -> [(String, String)]
getContent2 x  = map (\ m -> (x, m))

getContent4 :: [String] -> [String]
getContent4 = map ((!! 1) .  words)

getContent5 :: [String] -> [String]
getContent5  = map $ fst . break (== '(')

getContent6 :: [[String]] ->[[String]]
getContent6 = map $ filter (elem '.') . getContent5 . getContent4

isIn3 :: (Eq a) => [(a, a)] -> [(a, a)]
isIn3 = filter $ uncurry (/=)
