{-# LANGUAGE CPP #-}
{- |
Module      :$Header$
Description : CMDL interface commands
Copyright   : uni-bremen and DFKI
License     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

CMDL.InfoCommands contains all commands
that provides information about the state
of the development graph and selected
theories
-}

module CMDL.InfoCommands
       ( cNodes
       , cShowDgGoals
       , cDisplayGraph
       , cShowNodeProvenGoals
       , cShowNodeUnprovenGoals
       , cRedoHistory
       , cShowTaxonomy
       , cShowTheory
       , cShowTheoryGoals
       , cUndoHistory
       , cEdges
       , cShowNodeAxioms
       , cInfo
       , cInfoCurrent
       , cShowConcept
       , cNodeNumber
       , cHelp
       ) where


#ifdef UNI_PACKAGE
import Common.UniUtils
import GUI.Taxonomy
import GUI.ShowGraph
#endif

import CMDL.DataTypesUtils
import CMDL.DataTypes
import CMDL.Shell (nodeNames)
import CMDL.Utils (createEdgeNames, decomposeIntoGoals, obtainEdgeList,
                   obtainNodeList, prettyPrintErrList)

import Static.GTheory (G_theory(G_theory), BasicProof)
import Static.DevGraph
import Static.PrintDevGraph (showLEdge)

import Common.AS_Annotation (SenAttr(isAxiom))
import Common.DocUtils (showDoc)
import Common.Taxonomy (TaxoGraphKind(..))
import Common.Utils (trim)
import qualified Common.OrderedMap as OMap

import Data.Graph.Inductive.Graph (LNode, LEdge, Node)
import Data.List

import Logic.Prover (SenStatus)
import Logic.Comorphism (AnyComorphism)

import Driver.Options (defaultHetcatsOpts)

import Interfaces.Command (cmdNameStr, describeCmd, showCmd)
import Interfaces.DataTypes
import Interfaces.Utils (getAllEdges)

-- show list of all goals(i.e. prints their name)
cShowDgGoals :: CmdlState -> IO CmdlState
cShowDgGoals state
 = case i_state $ intState state of
    -- nothing to print
    Nothing -> return state
    Just dgState ->
     -- compute list of node goals
     let nodeGoals = nodeNames $ getAllGoalNodes state

         -- list of all nodes
         ls  = getAllNodes dgState
         lsGE= getAllGoalEdges state
         -- list of all goal edge names
         edgeGoals = createEdgeNames ls lsGE
     -- print sorted version of the list
      in return $ genMessage [] (unlines $ sort (nodeGoals ++ edgeGoals)) state


-- local function that computes the theory of a node but it
-- keeps only the goal theory
getGoalThS :: CmdlUseTranslation -> Int -> CmdlState -> [String]
getGoalThS useTrans x state
 = case getTh useTrans x state of
    Nothing -> []
    Just th ->
      let nwth = case th of
                  G_theory x1 x2 x3 thSens x4 ->
                    G_theory x1 x2 x3
                       (OMap.filter (\s-> not (isAxiom s) &&
                                          not (isProvenSenStatus s))
                       thSens) x4
      in [showDoc nwth "\n"]

--local function that computes the theory of a node
--that takes into consideration translated theories in
--the selection too and returns the theory as a string
getThS :: CmdlUseTranslation -> Int -> CmdlState -> [String]
getThS useTrans x state =
  case getTh useTrans x state of
    Nothing -> ["Could not find a theory"]
    Just th -> [showDoc th "\n"]

getInfoFromNodes :: String -> ([Node] -> [String]) -> CmdlState -> IO CmdlState
getInfoFromNodes input f state =
  case i_state $ intState state of
    Nothing      -> return state
    Just dgState -> let (errors, nodes) = getInputNodes input dgState
                     in return (if null nodes
                                  then genErrorMsg errors state
                                  else genMessage errors
                                         (intercalate "\n" $ f nodes) state)

cShowFromNode :: (forall a . SenStatus a (AnyComorphism, BasicProof) -> Bool)
                                     -- ^ what sentences to show
               -> String             -- input string containing node-names
               -> CmdlState          -- the state
               -> IO CmdlState
cShowFromNode f input state =
  getInfoFromNodes input (concatMap (\ n ->
                case getTh Do_translate n state of
                  Nothing -> []
                  Just th -> case th of
                                 G_theory _ _ _ sens _ -> OMap.keys $
                                   OMap.filter f sens)) state

cShowNodeProvenGoals :: String -> CmdlState -> IO CmdlState
cShowNodeProvenGoals =
  cShowFromNode (\ s -> not (isAxiom s) && isProvenSenStatus s)

cShowNodeUnprovenGoals :: String -> CmdlState -> IO CmdlState
cShowNodeUnprovenGoals =
  cShowFromNode (\ s -> not (isAxiom s) && not (isProvenSenStatus s))

cShowNodeAxioms :: String -> CmdlState -> IO CmdlState
cShowNodeAxioms = cShowFromNode isAxiom

-- show theory of input nodes
cShowTheory :: CmdlUseTranslation -> String -> CmdlState -> IO CmdlState
cShowTheory useTrans input state =
  getInfoFromNodes input (concatMap (\ n -> getThS useTrans n state)) state

-- show theory of all goals
cShowTheoryGoals :: String -> CmdlState -> IO CmdlState
cShowTheoryGoals input st =
  getInfoFromNodes input (concatMap (\ n -> getGoalThS Do_translate n st)) st

showNodeInfo :: LNode DGNodeLab -> String
showNodeInfo (i, l) =
  (if isDGRef l
     then ("reference " ++)
     else if isInternalNode l then ("internal " ++) else id)
  "node " ++ getDGNodeName l ++ " " ++ show i ++ "\n" ++ showDoc l ""

showEdgeInfo :: LEdge DGLinkLab -> String
showEdgeInfo e@(_, _, l) = showLEdge e ++ "\n" ++ showDoc l ""

-- show all information of selection
cInfoCurrent::CmdlState -> IO CmdlState
cInfoCurrent state =
  case i_state $ intState state of
    -- nothing selected
    Nothing -> return state
    Just ps -> let (errors, nodes) = getSelectedDGNodes ps
                in if null nodes
                     then return $ genErrorMsg errors state
                     else cInfo (intercalate " " $ nodeNames nodes) state

-- show all information of input
cInfo :: String -> CmdlState -> IO CmdlState
cInfo input state =
  case i_state $ intState state of
    -- error message
    Nothing -> return $ genErrorMsg "No library loaded" state
    Just dgS ->
     let (nds,edg,nbEdg,errs) = decomposeIntoGoals input
         tmpErrs = prettyPrintErrList errs
     in case (nds,edg,nbEdg) of
          ([],[],[]) -> return $ genErrorMsg ("Nothing from the input "
                                       ++"could be processed") state
          (_,_,_) ->
            let lsNodes = getAllNodes dgS
                lsEdges = getAllEdges dgS
                (errs'',listEdges) = obtainEdgeList edg nbEdg lsNodes lsEdges
                (errs',listNodes) = obtainNodeList nds lsNodes
                strsNode = map showNodeInfo listNodes
                strsEdge = map showEdgeInfo listEdges
                tmpErrs' = tmpErrs ++ prettyPrintErrList errs'
                tmpErrs''= tmpErrs'++ prettyPrintErrList errs''
             in return $ genMessage tmpErrs''
                         (intercalate "\n\n" (strsNode ++ strsEdge)) state

taxoShowGeneric:: TaxoGraphKind -> CmdlState
                      -> [LNode DGNodeLab] -> IO()
taxoShowGeneric kind state ls =
  case ls of
#ifdef UNI_PACKAGE
    (nb,nlab):ll ->
     case i_state $ intState state of
      Nothing -> return ()
      Just _ ->
       case getTh Do_translate nb state of
       -- the theory was computed
        Just th ->
         do
          -- display graph
          graph <- displayGraph kind
                    (showName $ dgn_name nlab) th
          case graph of
           -- if successfully displayed sync the two threads
           -- so that one does not loose control on the
           -- interface while the graph is displayed
           Just g ->
            do sync (destroyed g)
               -- go to next
               taxoShowGeneric kind state ll
           Nothing ->
               -- graph was not displayed, then just
               -- go to next
               taxoShowGeneric kind state ll
        -- theory couldn't be computed so just go next
        _ -> taxoShowGeneric kind state ll
#endif
    _ -> return ()

cShowTaxoGraph :: TaxoGraphKind -> String -> CmdlState -> IO CmdlState
cShowTaxoGraph kind input state =
  case i_state $ intState state of
    Nothing  -> return state
    Just dgState ->
      do
        let (errors, nodes) = getInputDGNodes input dgState
        taxoShowGeneric kind state nodes
        return $ genMessage errors [] state

cShowTaxonomy :: String -> CmdlState -> IO CmdlState
cShowTaxonomy = cShowTaxoGraph KSubsort

cShowConcept :: String -> CmdlState -> IO CmdlState
cShowConcept = cShowTaxoGraph KConcept

-- show node number of input
cNodeNumber :: String -> CmdlState -> IO CmdlState
cNodeNumber input state =
  case i_state $ intState state of
    Nothing -> return state
    Just dgState ->
      let (errors, nodes) = getInputDGNodes input dgState
          ls = map (\ (i, n) -> showName (dgn_name n) ++ " is node number " ++
                    show i) nodes
       in return $ genMessage errors (intercalate "\n" ls) state

-- print the name of all edges
cEdges::CmdlState -> IO CmdlState
cEdges state
 = case i_state $ intState state of
    Nothing -> return state
    Just dgState ->
     do
      -- list of all nodes
      let lsNodes = getAllNodes dgState
          -- compute all edges names
          lsEdg = getAllEdges dgState
          lsEdges = createEdgeNames lsNodes lsEdg
      -- print edge list in a sorted fashion
      return $ genMessage [] (intercalate "\n" $ sort lsEdges) state

cUndoHistory :: CmdlState -> IO CmdlState
cUndoHistory = return . cHistory True

cRedoHistory :: CmdlState -> IO CmdlState
cRedoHistory = return . cHistory False

cHistory :: Bool -> CmdlState -> CmdlState
cHistory isUndo state = genMessage []
  (unlines $ ((if isUndo then "Un" else "Re") ++ "do history :")
    : map (showCmd . command)
      ((if isUndo then undoList else redoList) $ i_hist $ intState state)
  ) state

-- print the name of all nodes
cNodes::CmdlState -> IO CmdlState
cNodes state
 = case i_state $ intState state of
    -- no library loaded, so nothing to print
    Nothing -> return state
    Just dgState ->
     do
     -- compute the list of node names
     let ls = nodeNames $ getAllNodes dgState
     -- print a sorted version of it
     return $ genMessage [] (intercalate "\n" $ sort ls) state

-- draw graph
cDisplayGraph::CmdlState -> IO CmdlState
cDisplayGraph state
 = case i_state $ intState state of
#ifdef UNI_PACKAGE
    Just dgState ->
     do
      -- obtain the name of the last loaded library for
      -- documentation/debugging reasons
      let flnm = fileLoaded $  prompter state
      showGraph flnm defaultHetcatsOpts ( Just
                   (i_ln dgState, i_libEnv dgState))
      return state
#endif
   -- no development graph present
    _ -> return state

cHelp :: [CmdlCmdDescription] -> CmdlState -> IO CmdlState
cHelp allcmds state = do
  putStrLn $ formatLine ("Command", "Parameter", "Description")
  putStrLn $ replicate maxLineWidth '-'
  mapM_ (\ cm -> do
                   let cmd = cmdDescription cm
                       name = cmdNameStr cmd
                       req = formatReq $ show $ cmdReq cm
                       descL = formatDesc $ describeCmd cmd
                       desc = head descL ++
                              concatMap ((++) ('\n' : replicate descStart ' '))
                              (tail descL)
                   putStrLn $ formatLine (name, req, desc)) allcmds
  return state
  where
    maxLineWidth = 80
    maxNameLen  = maximum $ map (length . cmdNameStr  . cmdDescription) allcmds
    maxParamLen = maximum $ map (length . formatReq   . show . cmdReq ) allcmds
    descStart = maxNameLen + 1 + maxParamLen + 1
    descWidth = maxLineWidth - descStart
    formatReq :: String -> String
    formatReq r = if null r then "" else '<' : r ++ ">"
    formatDesc :: String -> [String]
    formatDesc = reverse . filter (not . null) . map trim .
                 foldl (\ l w -> if length (head l) + length w > descWidth
                                   then (w ++ " ") : l
                                   else (head l ++ w ++ " ") : tail l)
                       [""] . words
    formatLine :: (String, String, String) -> String
    formatLine (c1, c2, c3) =
      c1 ++ replicate (maxNameLen  - length c1 + 1) ' ' ++
      c2 ++ replicate (maxParamLen - length c2 + 1) ' ' ++ c3
