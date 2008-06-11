{- |
Module      :$Header$
Description : shell related functions
Copyright   : uni-bremen and DFKI
License     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

PGIP.Shell contains almost all functions related the
the CMDL shell or shellac

-}

module PGIP.Shell
       ( shellacCmd
       , cDetails
       , cComment
       , cOpenComment
       , cCloseComment
       , nodeNames
       , register2history
       , checkCom
       , subtractCommandName
       , getTypeOf
       , cmdlCompletionFn
       ) where

import PGIP.DataTypes
import PGIP.Utils
import PGIP.DataTypesUtils
import Logic.Comorphism
import Logic.Grothendieck
import Logic.Prover
import Logic.Logic
import Comorphisms.LogicGraph
import Proofs.AbstractState
import Control.Monad.Trans
import Data.List
import Directory
import Static.DevGraph
import Static.GTheory
import System.IO
import System.Console.Shell.ShellMonad
import qualified Common.OrderedMap as OMap

-- | Creates a shellac command
shellacCmd :: CMDL_CmdDescription -> Sh CMDL_State ()
shellacCmd cmd
 = do
    newState<- getShellSt >>= \state -> liftIO(checkCom cmd state {
                                                     output = (output state){
                                                           errorMsg = [],
                                                           outputMsg = [],
                                                           fatalError = False
                                                           }
                                                      })
    let result = output newState
    if errorMsg result /= []
      then shellPutErrLn
               ("The following error(s) occured :\n"++(errorMsg result))
      else return ()
    if outputMsg result /= []
      then shellPutStrLn $ outputMsg result
      else return ()
    putShellSt newState


register2history :: CMDL_CmdDescription -> CMDL_State -> CMDL_State
register2history dscr state
 = let oldHistory = history state
   in case cmdType $ cmdInfo dscr of
       UndoRedoCmd -> state
       _ -> state {
                 history = oldHistory {
                            undoList = (cmdInfo dscr): (undoList oldHistory),
                            redoList = []
                            }
                 }

-- | Checks if a command needs to be executed or skiped
checkCom :: CMDL_CmdDescription -> CMDL_State -> IO CMDL_State
checkCom descr state
 = do
    -- pC processes a comment line checking if it is the end of the comment
    -- returns the corresponding state
    let pC st inp = case isInfixOf "}%" inp of
                                      True -> st {openComment = False}
                                      False -> st
     -- obtains the function that needs to be called (if it requires input
     -- insert the input into the function
        getFn dsc = case cmdFn dsc of
                     CmdNoInput fn -> fn
                     CmdWithInput fn -> fn (cmdInput $ cmdInfo dsc)
    -- adds a line into the script (composed of command name and input)
        addSp st ps nm p = st {
                            proveState = Just ps {
                              script = ((script ps)++nm++" "++p++"\n") } }
    -- check the priority of the current command
    case cmdPriority descr of
     -- command has no priority
     CmdNoPriority ->
      -- check if there is a prove state
      case proveState state of
       -- no prove state,
       Nothing ->
         -- check for comment
        if openComment state == True then return $ pC state $
                                                   cmdInput $ cmdInfo descr
                                     else
                                       do
                                        nwSt <- (getFn descr) state
                                        return $register2history descr nwSt
         -- else see if it is inside a script
       Just pS ->
        if loadScript pS == False
         then if openComment state ==True then return$pC state$
                                                      cmdInput$ cmdInfo descr
                                           else
                                            do
                                             nwSt <- (getFn descr) state
                                             return$ register2history
                                                               descr nwSt
         else return $ addSp state pS (head $ cmdNames $ cmdInfo descr)
                                         (cmdInput $ cmdInfo descr)
     CmdGreaterThanComments ->
      case proveState state of
       Nothing -> do
                   nwSt <- (getFn descr) state
                   return $ register2history descr nwSt
       Just pS ->
         if loadScript pS == False then
                                    do nwSt <- (getFn descr) state
                                       return$ register2history descr nwSt
                else return $ addSp state pS (head $ cmdNames$ cmdInfo descr)
                                             (cmdInput $ cmdInfo descr)
     CmdGreaterThanScriptAndComments -> do
                                      nwSt <- (getFn descr) state
                                      return $ register2history descr nwSt



-- | Prints details about the syntax of the interface
cDetails :: CMDL_State -> IO CMDL_State
cDetails state
 = do
    return state {
            output = CMDL_Output {
               errorMsg = "",
               outputMsg = printDetails,
               fatalError = False
                        }
            }

-- | Function handle a comment line
cComment::String -> CMDL_State -> IO CMDL_State
cComment _ state
 = return state


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

cOpenComment :: String -> CMDL_State -> IO CMDL_State
cOpenComment _ state
 = return state { openComment = True }

cCloseComment :: CMDL_State -> IO CMDL_State
cCloseComment state
 = return state { openComment = False }


-- | given an input it assumes that it starts with a
-- command name and tries to remove this command name
subtractCommandName::[CMDL_CmdDescription] -> String -> String
subtractCommandName allcmds input
 =let inp = trimLeft input
      lst = concatMap(\x -> case find(\y -> isPrefixOf y inp)$
                                            cmdNames $ cmdInfo x of
                             Nothing -> []
                             Just tmp -> [tmp]) allcmds
  in drop (length $ head lst) inp

-- | The function determines the requirements of the command
-- name found at the begining of the string
getTypeOf::[CMDL_CmdDescription] -> String -> CMDL_CmdRequirements
getTypeOf allcmds input
 = let nwInput = trim input
       tmp =concatMap(\x ->
                       case find(\y -> isPrefixOf y nwInput)$
                                             cmdNames$ cmdInfo x of
                        Nothing -> []
                        Just _ -> [cmdReq x]) allcmds
   in case tmp of
       result:[] -> result
       _         -> ReqUnknown

nodeNames :: [(a, DGNodeLab)] -> [String]
nodeNames = map (showName . dgn_name . snd)

-- | The function provides a list of possible completion
-- to a given input if any
cmdlCompletionFn :: [CMDL_CmdDescription] -> CMDL_State
                    -> String -> IO [String]
cmdlCompletionFn allcmds allState input
 =do
  case getTypeOf allcmds input of
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
           allNames = nodeNames (getAllNodes state)
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
           allNames = nodeNames (getAllGoalNodes allState state)
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
                      subtractCommandName allcmds input
          -- what is before this list
           bC = reverse $ trimLeft $ drop (length tC)
                     $ trimLeft $ reverse input
          -- get all nodes
           ls = getAllNodes state
          -- get all edges
           lsE= getAllEdges state
          -- get all edge names
           allNames = createEdgeNames ls lsE
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
                      subtractCommandName allcmds input
           bC = reverse $ trimLeft $ drop (length tC)
                     $ trimLeft $ reverse input
           ls  = getAllNodes state
           lsGE= getAllGoalEdges state
           allNames = createEdgeNames ls lsGE
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
           filteredNodes=map (\y -> bCN++" "++y) $
                          filter (\x->isPrefixOf tCN x)
                                  $ nodeNames allnodes
           tCE = unfinishedEdgeName $
                     subtractCommandName allcmds input
           bCE = reverse $ trimLeft $ drop (length tCE)
                      $ trimLeft $ reverse input
         -- same as in the ReqEdge case
           edgeNames = createEdgeNames allnodes alledges
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
           filteredNodes=map (\y -> bCN++" "++y) $
                          filter(\x->isPrefixOf tCN x)
                                $ nodeNames (getAllGoalNodes allState state)
           tCE = unfinishedEdgeName $
                     subtractCommandName allcmds input
           bCE = reverse $ trimLeft $ drop (length tCE)
                     $ trimLeft $ reverse input
          -- same as in the ReqEdge case
           edgeNames =createEdgeNames allnodes allGE
           filteredEdges=map (\y -> bCE++" "++y) $
                          filter(\x->isPrefixOf tCE x)
                                             edgeNames
          --sum up the two cases
       return (filteredNodes ++ filteredEdges )
   ReqConsCheck ->
      do
       let tC = case isWhiteSpace $ lastChar input of
                 True -> []
                 False -> lastString $ words input
           bC = case isWhiteSpace $ lastChar input of
                 True -> trimRight input
                 False -> unwords $ init $ words input
           addConsCheckers acc cm =
            case cm of
             Comorphism cid -> acc ++
                 foldl (\ l p -> if hasProverKind
                                      ProveCMDLautomatic p
                                 then (G_cons_checker
                                        (targetLogic cid) p):l
                                 else l)
                 []
                 (cons_checkers $ targetLogic cid)
           getPName' x = case x of
                          (G_cons_checker _ p) -> prover_name p
           getConsCheckersAutomatic cm = foldl addConsCheckers [] cm
           createConsCheckersList cm = map (\x -> getPName' x)
                                         (getConsCheckersAutomatic cm)
       case  proveState allState of
        Nothing ->
         -- not in proving mode !? you can not choose a consistency
         -- checker here
               return []
        Just proofState ->
         case cComorphism proofState of
          -- some comorphism was used
          Just c-> return $ map (\y->bC++" "++y) $
                    filter (\x->isPrefixOf tC x) $ createConsCheckersList [c]
          Nothing ->
           case elements proofState of
            -- no elements selected
            [] -> return []
            c:_ ->
             do
              case c of
               Element z _ -> return $ map(\y->bC++" "++y)
                               $ filter (\x->isPrefixOf tC x)
                               $ createConsCheckersList
                               $ findComorphismPaths
                                 logicGraph
                                   (sublogicOfTh $ theory z)
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
        case proveState allState of
         Nothing -> return []
         Just pS ->
          case elements pS of
           [] -> return []
           (Element st _):_ ->
              let tC = case isWhiteSpace $ lastChar input of
                        True -> []
                        False ->lastString $ words input
                  bC = case isWhiteSpace $ lastChar input of
                        True -> trimRight input
                        False-> unwords $ init $ words input
                  cL = concatMap ( \(Comorphism cid) ->
                              case (language_name $ sourceLogic cid) ==
                                     (language_name $ logicId st) of
                                False -> []
                                True -> [ language_name cid ]
                             ) comorphismList
              in return $ map (\y -> bC++" "++y)
                        $ filter (\x->isPrefixOf tC x) cL
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
   ReqAxm ->
     do
      case proveState allState of
       Nothing-> return []
       Just pS->
        do
         let tC =  case isWhiteSpace $ lastChar input of
                    True -> []
                    False-> lastString $ words input
             bC = case isWhiteSpace $ lastChar input of
                    True -> trimRight input
                    False -> unwords $ init $ words input
         return $ map(\y-> bC++" "++y) $
          filter (\x -> isPrefixOf tC x) $ nub $
          concatMap(\(Element st _)->
                 case theory st of
                  G_theory _ _ _ aMap _ ->
                   OMap.keys aMap ) $ elements pS
   ReqGoal ->
     do
      case proveState allState of
       Nothing-> return []
       Just pS ->
        do
         let tC = case isWhiteSpace $ lastChar input of
                   True -> []
                   False -> unwords $ init $ words input
             bC = case isWhiteSpace $ lastChar input of
                   True -> trimRight input
                   False-> unwords $ init $ words input
         return $ map (\y->bC++" "++y) $
          filter(\x-> isPrefixOf tC x) $ nub $
          concatMap(\(Element st _)->
                       OMap.keys $ goalMap st) $ elements pS
   ReqNumber -> do
                  let lst = words input
                  case length lst of
                   1 -> return $ map(\x -> (lst!!0)++" "++x)
                                  ["0","1","2","3","4","5","6","7","8","9"]
                   2 -> case isWhiteSpace$lastChar input of
                          True -> return []
                          False ->return $ map(\x -> input ++ x)
                                    ["0","1","2","3","4","5","6","7","8","9"]
                   _ -> return []
   ReqNothing -> do return []
   ReqUnknown ->
     do
       return []

