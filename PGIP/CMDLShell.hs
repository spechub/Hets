{- |
Module      :$Header$
Description : shell related functions
Copyright   : uni-bremen and DFKI
Licence     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@iu-bremen.de
Stability   : provisional
Portability : portable

PGIP.CMDLShell contains almost all functions related the
the CMDL shell or shellac
-} 


module PGIP.CMDLShell
       ( shellComWith
       , shellComWithout
       , shellDetails
       , shellComment
       , cmdlEvalFunc
       , cmdlFileEvalFunc
       , cmdlCompletionFn
       )where

import PGIP.CMDLUtils
import PGIP.CMDLState

-- liftIO function
import Control.Monad.Trans
import System.IO  

import Data.List
import Static.DevGraph
import Logic.Comorphism
import Logic.Grothendieck
import Logic.Prover
import Logic.Logic
import Comorphisms.LogicGraph
import System.Directory

-- shellac function
import System.Console.Shell.ShellMonad


import Proofs.AbstractState

-- | General shell command that uses string input
shellComWith :: (String->CMDLState -> IO CMDLState)
                  -> String -> Sh CMDLState ()
shellComWith fn input
 = do
    -- get rid of comments from input
    let s = stripComments input
    -- apply command and create new state
    newState <- getShellSt >>= \state -> liftIO( fn s state)
    -- check if any error occured in executing command
    case errorMsg newState of
     [] ->
          -- insert the new state into the interface
          putShellSt newState
     msg -> do
           -- print the error using the shellac specific 
           -- function
           shellPutErrLn ("Error : "++msg)
           -- insert the new state without errors into the
           -- interface
           putShellSt newState {
                        errorMsg = []
                        }


-- | General shell command that does not use an input
shellComWithout :: (CMDLState -> IO CMDLState)
                      -> Sh CMDLState ()
shellComWithout fn
 = do
    -- apply command and create new state
    newState <- getShellSt >>= \state -> liftIO (fn state)
    -- check if any error occured in executing command
    case errorMsg newState of
     [] -> 
           -- insert the new state into the interface
           putShellSt newState
     s  -> do
            --print the error using the shellac specific
            --function
            shellPutErrLn ("Error : "++s)
            -- insert the new state without errors into the
            -- interface
            putShellSt newState {
                          errorMsg = []
                          }
    
-- | Prints details about the syntax of the interface
shellDetails :: Sh CMDLState ()
shellDetails
 = do
    shellPutStr printDetails

-- | Function handle a comment line
shellComment::String -> Sh CMDLState ()
shellComment _
 =
  -- do nothing
  do val<- getShellSt 
     putShellSt val


-- | Produces a string containing a detailed description
-- of the interface grammar
printDetails :: String
printDetails =
 "\n\n Hets Interactive mode.The available grammar is\n\n" ++
 "   use [PATH]              -- open a file with a HetCASL"++
 " library\n" ++
 "                           -- this will compute a "++
 "development graph\n" ++
 "                           -- and a list of open proof"++
 " obligations\n" ++
 "   dg [DG-COMMAND] [GOAL*] -- apply a proof step of the"++
 " dg calculus\n" ++
 "   dg-all [DG-COMMAND]     -- same as dg, but for all"++
 " open goals\n" ++
 "   show-dg-goals           -- display list of open dg"++
 " goals\n" ++
 "   show-theory-goals       -- display list of theory"++
 " goals\n" ++
 "   show-theory             -- show current theory and"++
 " proof goals\n" ++
 "   node-info               -- show info about current\n" ++
 "                           -- dg node (name, origin,"++
 " sublogic)\n"++
 "   show-taxonomy           -- show taxonomy graph\n" ++
 "   show-concepts           -- show conecpt graph\n" ++
 "   translate [COMORPHISM]  -- translate theory goals \n" ++
 "                           -- along comorphism\n" ++
 "   prover [PROVER]         -- select a prover\n" ++
 "   proof-script [FORMULA] [PROOF-SCRIPT] end-script\n" ++
 "                           -- process proof script for"++
 " one goal\n" ++
 "   cons-check PROVER       -- check consistency\n" ++
 "   prove [FORMULA*] [AXIOM-SELECTION?]\n" ++
 "   prove-all [AXIOM-SELECTION?]\n" ++
 "   q/quit/exit             -- exit hets\n\n" ++
 " AXIOM-SELECTION ::=\n" ++
 "   with FORMULA+           -- include only specified"++
 " axioms\n" ++
 "   exlcuding FORMULA+      -- exlcude specified"++
 " axioms\n\n" ++
 " PROOF-SCRIPT        -- can be anything (prover"++
 " specific)\n" ++
 "                     -- the end is recognized with"++
 " \"end-script\"\n\n" ++
 " DG-COMMAND ::= \n" ++
 "     auto          -- automatic tactic\n" ++
 "     glob-subsume -- global subsumption\n" ++
 "     glob-decomp  -- global decomposition\n"++
 "     loc-infer    -- local inference\n"++
 "     loc-decomp   -- local decomposition\n"++
 "     comp         -- composition\n"++
 "     comp-new     -- composition with speculation of"++
 " new egdes\n"++
 "     hide-thm     -- Hide-Theorem-Shift\n"++
 "     thm-hide     -- Theorem-Hide-Shift\n"++
 "     basic        -- start proving at a particular"++
 " node,\n"++
 "                  -- i.e. start local proving in a"++
 " theory\n\n"++
 " GOAL ::=  \n"++
 "   NODE                   -- select local goals at a"++
 " node\n"++
 "   NODE -> NODE           -- select all edges between"++
 " two given nodes\n"++
 "   NODE - DIGIT* -> NODE  -- select specific edge"++
 " between two nodes\n"++
 "\n NODE ::= \n"++
 "     ID         -- specify nodes with their names\n\n"++
 " COMORPHISM ::= ID ; ... ; ID    -- composite of basic"++
 " comorphisms\n\n"++
 " PROVER ::= ID                   -- name of prover\n\n"++
 " FORMULA ::= ID                  -- label of formula\n\n"++
 " ID ::=                          -- identifier (String)\n\n"

-- For normal keyboard input 


-- | The function is called everytime when the input could 
-- not be parsed as a command
cNotACommand :: String -> CMDLState -> IO CMDLState
cNotACommand input state
 = do
    case input of 
     -- if input line is empty do nothing
     [] -> return state
     -- anything else treat as an error for now
     s -> return state {
                   errorMsg = "input line " ++ s
                   }

-- | The evaluation function is called when the input could 
-- not be parsed as a command. 
cmdlEvalFunc :: String -> Sh CMDLState ()
cmdlEvalFunc 
 = shellComWith cNotACommand 


-- For file input

-- | The function is called everytime when the input could
-- not be parsed as a command
cNotACommandFile :: String-> CMDLState -> IO CMDLState
cNotACommandFile input state
 = do
    case input of
     -- if input line is empty do nothing
     [] -> return state
     -- anything else treat as an error for now
     s -> return state {
                   errorMsg = "input line "++s
                   }

-- |The evaluation function for a file input is called
-- when a line from the file could not be interpreted
cmdlFileEvalFunc :: String -> Sh CMDLState ()
cmdlFileEvalFunc
 = shellComWith cNotACommandFile


-- | The function returns a list of all possible commands
-- name and associate requirements
allCommandsName:: [(String,CommandTypes)]
allCommandsName
 = ("use",ReqFile)
 : ("dg auto",ReqEdges)
 : ("dg glob-subsume",ReqEdges)
 : ("dg glob-decomp",ReqEdges)
 : ("dg loc-infer",ReqEdges)
 : ("dg loc-decomp",ReqEdges)
 : ("dg dg comp",ReqEdges)
 : ("dg comp-new",ReqEdges)
 : ("dg hide-thm",ReqEdges)
 : ("dg thm-hide",ReqNodes)
 : ("select",ReqNodes)
 : ("dg basic",ReqNodes)
 : ("info",ReqNodesAndEdges)
 : ("show-taxonomy", ReqNodes)
 : ("show-concept", ReqNodes)
 : ("node-number", ReqNodes)
 : ("show-theory", ReqNodes)
 : ("translate", ReqComorphism)
 : ("prover", ReqProvers) 
 : []

-- | given an input it assumes that it starts with a 
-- command name and tries to remove this command name
subtractCommandName::String -> String
subtractCommandName input
 =let inp = trimLeft input 
  in case find (\(x,_) -> isPrefixOf x input)
                  allCommandsName of
       Nothing -> inp
       Just (x,_) -> drop (length x) inp

-- | The function determines the type of the command
-- name found at the begining of the string
getTypeOf::String -> CommandTypes
getTypeOf input
 = let nwInput = trim input 
       tmp =concatMap(\(x,y) -> case isPrefixOf x nwInput of
                                 True -> [y]
                                 False-> []) allCommandsName
   in case tmp of
       result:[] -> result
       _         -> ReqUnknown


-- | The function provides a list of possible completion
-- to a given input if any
cmdlCompletionFn :: CMDLState -> String -> IO [String]
cmdlCompletionFn allState input
 =do
  case getTypeOf input of 
   ReqNodes ->
    case devGraphState allState of
     Nothing -> return []
     Just state ->
      do
       -- a pair, where the first element is what needs
       -- to be completed while the second is what is 
       -- before the word that needs to be completed
       let (tC,bC) = case isWhiteSpace $ lastChar input of
                        -- if last character is a white space
                        -- then there is no word to complete
                         True  -> ([], trimRight input)
                        -- otherwise is just the last word
                        -- from the input
                         False -> (lastString $ words input,
                                   unwords $ init 
                                   $ words input)
          -- get all node names              
           allNames = map (\x -> case x of
                                 (_,DGNode t _ _ _ _ _ _ ) ->
                                   showName t
                                 (_,DGRef t _ _ _ _ _) ->
                                   showName t) (getAllNodes
                                                       state)
      -- filter out words that do not start with the word
      -- that needs to be completed and add the word that
      -- was before the word that needs to be completed
       let res = map (\y -> bC++" "++y) $
                  filter (\x -> isPrefixOf tC x) allNames
       return res
   ReqGNodes ->
    case devGraphState allState of
     Nothing-> return []
     Just state ->
      do
        --the last unfinished word that needs to be 
        --completed and what is before it
       let (tC,bC) = case isWhiteSpace $ lastChar input of
                        -- if last character is a white space
                        -- then there is no word to complete
                         True -> ([], trimRight input)
                        -- otherwise is just the last word
                        -- from the input
                         False -> (lastString $ words input,
                                   unwords $ init
                                   $ words input)
          -- get all goal node names
           allNames = map (\x -> case x of 
                                 (_,DGNode t _ _ _ _ _ _ ) ->
                                  showName t
                                 (_,DGRef t _ _ _ _ _) ->
                                  showName t) (getAllGoalNodes
                                                      state)
      -- filter out words that do not start with the word
      -- that needs to be completed
       return $ map(\y -> bC++" "++y) $
           filter(\x -> isPrefixOf tC x) allNames
   ReqEdges ->
    case devGraphState allState of
     Nothing -> return []
     Just state ->
      do
      --the last unfinished edge name that needs to be 
      --completed
       let tC = unfinishedEdgeName $ 
                      subtractCommandName input
          -- what is before this list
           bC = reverse $ trimLeft $ drop (length tC) 
                     $ trimLeft $ reverse input
          -- get all nodes
           ls = getAllNodes state
          -- get all edges
           lsE= getAllEdges state
          -- get all edge names
           allNames = createEdgeNames ls lsE lsE
      -- filter out words that do not start with the word 
      -- that needs to be completed
       let res = map (\y -> bC++ " "++y) $
                  filter(\x->isPrefixOf tC x) allNames
       return res
   ReqGEdges ->
    case devGraphState allState of
     Nothing -> return []
     Just state ->
      do
      -- the last unfinished edge name that needs to be 
      -- completed
       let tC = unfinishedEdgeName  $ 
                      subtractCommandName input
           bC = reverse $ trimLeft $ drop (length tC)
                     $ trimLeft $ reverse input
           ls  = getAllNodes state
           lsE = getAllEdges state
           lsGE= getAllGoalEdges state
           allNames = createEdgeNames ls lsE lsGE
          -- filter out words that do not start with the word
          -- that needs to be completed
       return $ map (\y -> bC++" "++y) $
           filter(\x-> isPrefixOf tC x) allNames
   ReqNodesAndEdges ->
    case devGraphState allState of
     Nothing -> return []
     Just state ->
      do
       let allnodes = getAllNodes state
           alledges = getAllEdges state
           penultimum s=lastString $ reverse $ safeTail 
                                   $ reverse s
          -- same as in the ReqNode case just that we need
          -- to take care that the word we trying to complete
          -- can also be a node name not only an edge name
           (tCN,bCN) = case isWhiteSpace $ lastChar input of 
                         True -> 
                          case lastString $ words input of
                           -- we are in the middle of an
                           -- edge, we shouldn't look for
                           -- node names
                           "->" -> ("Impossible to complete",
                                     [])
                           -- it may be a node 
                           _ -> ([], trimRight input)
                         False -> 
                          case penultimum $ words input of
                           "->" -> ("Impossible to complete",
                                    [])
                           _ -> (lastString $ words input,
                                 unwords $ init
                                 $ words input)
           nodeNames = map (\x -> case x of 
                                  (_, DGNode t _ _ _ _ _ _) ->
                                    showName t
                                  (_, DGRef t _ _ _ _ _) ->
                                    showName t) allnodes
           filteredNodes=map (\y -> bCN++" "++y) $
                          filter (\x->isPrefixOf tCN x)
                                   nodeNames
           tCE = unfinishedEdgeName $
                     subtractCommandName input
           bCE = reverse $ trimLeft $ drop (length tCE)
                      $ trimLeft $ reverse input
         -- same as in the ReqEdge case
           edgeNames = createEdgeNames allnodes alledges 
                                      alledges
           filteredEdges=map (\y -> bCE++" "++y) $ 
                          filter (\x->isPrefixOf tCE x)
                                               edgeNames
      -- sum up the two cases                          
       return (filteredNodes ++ filteredEdges )           
   ReqGNodesAndGEdges ->
    case devGraphState allState of
     Nothing -> return []
     Just state ->
      do
       let allnodes = getAllNodes state
           allE = getAllEdges state
           allGE= getAllGoalEdges state
           penultimum s=lastString $ reverse $ safeTail 
                                   $ reverse s
          -- same as in the ReqNode case just that we need 
          -- to take care that the word we trying to complete
        -- can also be a node name not only an edge name
           (tCN,bCN) = case isWhiteSpace $ lastChar input of
                          True ->
                           case lastString $ words input of
                           -- we are in the middle of an
                           -- edge, we shouldn't look for
                           -- node names
                            "->" ->("Impossible to complete",
                                     [])
                           --it may be a node
                            _ -> ([], trimRight input)
                          False ->
                           case penultimum $ words input of
                            "->" ->("Impossible to complete",
                                    [])
                            _ -> (lastString $ words input,
                                  unwords $ init $
                                  words input)
           nodeNames =map(\x-> case x of
                               (_,DGNode t _ _ _ _ _ _) ->
                                showName t
                               (_, DGRef t _ _ _ _ _) ->
                                showName t) (getAllGoalNodes
                                                   state)
           filteredNodes=map (\y -> bCN++" "++y) $ 
                          filter(\x->isPrefixOf tCN x)
                                     nodeNames
           tCE = unfinishedEdgeName $
                     subtractCommandName input
           bCE = reverse $ trimLeft $ drop (length tCE)
                     $ trimLeft $ reverse input
          -- same as in the ReqEdge case
           edgeNames =createEdgeNames allnodes allE allGE
           filteredEdges=map (\y -> bCE++" "++y) $ 
                          filter(\x->isPrefixOf tCE x)
                                             edgeNames
          --sum up the two cases
       return (filteredNodes ++ filteredEdges )  
   ReqProvers ->    
      do
       let tC = case isWhiteSpace $ lastChar input of
                 True -> []
                 False-> lastString $ words input
           bC = case isWhiteSpace $ lastChar input of
                 True -> trimRight input
                 False->unwords $ init $ words input
           addProvers acc cm =
            case cm of
            Comorphism cid -> acc ++
                foldl (\ l p ->if hasProverKind 
                                    ProveCMDLautomatic p
                               then (G_prover 
                                       (targetLogic cid)
                                                       p):l
                               else l)
                []
                (provers $ targetLogic cid)
           -- this function is identical to the one defined
           -- in Proofs.InferBasic, but it is redone here 
           -- because InferBasic does not compile without
           -- UNI_PACKAGE
           getPName' x = case x of
                          (G_prover _ p)-> prover_name p
      -- from the given comorphism generate a list of 
      -- provers that can be applied to theories in that
      -- comorphism
           getProversCMDLautomatic cm=foldl addProvers [] cm
           createProverList cm = map (\x -> getPName' x) 
                             (getProversCMDLautomatic cm)
      -- find the last comorphism used if none use the 
      -- the comorphism of the first selected node
       case proveState allState of
        Nothing ->
       -- not in proving mode !? you can not choose 
       -- provers here
                return []
        Just proofState ->
         case cComorphism proofState of 
          -- some comorphism was used 
          Just c-> return $ map (\y -> bC++" "++y) $
                     filter (\x->isPrefixOf tC x)
                                      $ createProverList [c]
          Nothing -> 
           case elements proofState of  
             -- no elements selected 
             [] -> return []
             -- use the first element to get a comorphism
             c:_ -> 
               case c of
                Element z _->return $ map (\y -> bC++" "++y) 
                              $ filter (\x->isPrefixOf tC x)
                              $ createProverList 
                              $ findComorphismPaths
                                logicGraph 
                                  (sublogicOfTh $ theory z)
   ReqComorphism ->
       do
        let tC = case isWhiteSpace $ lastChar input of
                  True -> []
                  False ->lastString $ words input
            bC = case isWhiteSpace $ lastChar input of
                  True -> trimRight input
                  False-> unwords $ init $ words input
        return $ map (\y -> bC++" "++y) 
               $ filter (\x->isPrefixOf tC x)
               $ map (\(Comorphism cid) -> language_name cid) 
                          comorphismList
   ReqFile ->
      do
        -- the incomplete path introduced until now
        let initwd = case isWhiteSpace $ lastChar input of
                      True -> []
                      False -> lastString $ words input
        -- the folder in which to look for (it might be 
        -- empty)
            tmpPath=reverse $ dropWhile(\x ->case x of
                                              '/' -> False
                                              _   -> True
                                         ) $ reverse initwd
        -- in case no folder was introduced yet look into
        -- current folder
            lastPath = case tmpPath of
                       [] -> "./"
                       _  -> tmpPath
        -- the name of file/directory that needs to be 
        -- completed from the already introduced path
            tC=reverse $ takeWhile(\x -> case x of
                                          '/' -> False
                                          _   -> True
                                       ) $ reverse initwd
            bC = case isWhiteSpace $ lastChar input of
                  True -> input
                  False -> (unwords $ init $ words input)
                                 ++" "++tmpPath
        -- leave just folders and files with extenstion .casl
        b' <- doesDirectoryExist lastPath
        ls <- case b' of
               True -> getDirectoryContents lastPath
               False -> return []
        names<- fileFilter lastPath ls []
        -- case list contains only one name
        -- then if it is a folder extend it
        let names' = filter (\x->isPrefixOf tC x) names
        names''<- case safeTail names' of
                   -- check PGIP.CMDLUtils to see how it 
                   -- works, function should be done with
                   -- something like map but that can handle
                   -- functions with IO 
                   -- (mapIO !? couldn't make it work though)
                   [] -> fileExtend lastPath names' []
                   _  -> return names'
        return $ map (\y -> bC++y) names''
   ReqUnknown ->
     do
       return []

