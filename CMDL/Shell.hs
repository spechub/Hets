{- |
Module      : $Header$
Description : shell related functions
Copyright   : uni-bremen and DFKI
License     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

CMDL.Shell contains almost all functions related the
the CMDL shell or shellac

-}

module CMDL.Shell
       ( shellacCmd
       , cDetails
       , cComment
       , cOpenComment
       , cCloseComment
       , nodeNames
       , checkCom
       , subtractCommandName
       , getTypeOf
       , cmdlCompletionFn
       ) where

import Interfaces.Command
import Interfaces.DataTypes
import Interfaces.Utils
import Interfaces.GenericATPState
import CMDL.DataTypes
import CMDL.Utils
import CMDL.DataTypesUtils
import Logic.Comorphism
import Logic.Grothendieck
import Logic.Prover
import Logic.Logic
import Comorphisms.LogicGraph
import Proofs.AbstractState
import Control.Monad.Trans
import Data.Char (isSpace)
import Data.List
import System.Directory
import Static.DevGraph
import Static.GTheory
import System.IO
import System.Console.Shell.ShellMonad
import qualified Common.OrderedMap as OMap
import Common.AS_Annotation
import Common.Utils (trimLeft, trimRight)

-- | Creates a shellac command
shellacCmd :: CMDL_CmdDescription -> Sh CMDL_State ()
shellacCmd cmd
 = do
    newState<- getShellSt >>= \state -> liftIO(checkCom cmd state {
                                                     output = (output state){
                                                           errorMsg = [],
                                                           outputMsg = [],
                                                           warningMsg = []
                                                           }
                                                      })
    let result = output newState
    if errorMsg result /= []
      then shellPutErrLn
               ("The following error(s) occured :\n"++(errorMsg result))
      else return ()
    if warningMsg result /= []
      then shellPutErrLn
               ("The following warning(s) occured :\n"++(warningMsg result))
      else return ()
    if outputMsg result /= []
      then shellPutStrLn $ outputMsg result
      else return ()
    putShellSt newState


register2history :: CMDL_CmdDescription -> IO CMDL_State -> IO CMDL_State
register2history dscr state_io
 = do
    state <- state_io
    let oldHistory = i_hist $ intState  state
    case undoList oldHistory of
       [] -> return state
       h : r -> case command h of
               CommentCmd _ ->do
                     let nwh = h {
                                command = cmdDescription dscr }
                     return $ state {
                         intState = (intState state) {
                            i_hist = oldHistory {
                               undoList = nwh : r,
                               redoList = []
                             } } }
               _ -> return state


-- process a comment line
processComment :: CMDL_State -> String -> CMDL_State
processComment st inp
 = case isInfixOf "}%" inp of
    True -> st { openComment = False }
    False -> st

-- gets the function
getFn :: CMDL_CmdDescription -> (CMDL_State -> IO CMDL_State)
getFn desc
 = case cmdFn desc of
    CmdNoInput fn -> fn
    CmdWithInput fn -> fn (cmdInput desc)

-- adds a line to the script
addToScript :: CMDL_State -> IntIState -> String -> CMDL_State
addToScript st ist str
 = let olds = script ist
       oldextOpts = ts_extraOpts olds
   in st {
        intState = (intState st) {
                     i_state = Just ist {
                       script = olds { ts_extraOpts = str:oldextOpts } }
          } }


checkCom :: CMDL_CmdDescription -> CMDL_State -> IO CMDL_State
checkCom descr state
  =
    --check the priority of the current command
    case cmdPriority descr of
     CmdNoPriority ->
      -- check if there is open comment
      case openComment state of
       True -> return $ processComment state $ cmdInput descr
       False ->
        case i_state $ intState state of
         Nothing -> register2history descr $ (getFn descr) state
         Just ist ->
          -- check if there is inside a script
          case loadScript ist of
           False->register2history descr $ (getFn descr) state
           True->return $ addToScript state ist
                         (cmdName descr ++ " " ++ cmdInput descr)
     CmdGreaterThanComments ->
      case i_state $ intState state of
       Nothing -> register2history descr $ (getFn descr) state
       Just ist ->
        case loadScript ist of
         False -> register2history descr $ (getFn descr) state
         True ->return $ addToScript state ist
                        (cmdName descr ++ " " ++ cmdInput descr)
     CmdGreaterThanScriptAndComments ->
        (getFn descr) state



-- | Prints details about the syntax of the interface
cDetails :: CMDL_State -> IO CMDL_State
cDetails state
 = return state {
            output = CMDL_Message {
               errorMsg = [],
               outputMsg = printDetails,
               warningMsg = []
                        }
            }

-- | Function handle a comment line
cComment::String -> CMDL_State -> IO CMDL_State
cComment _ = return


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
      lst = concatMap(\ x -> case find(\y -> isPrefixOf y inp)
                                            [cmdName x] of
                             Nothing -> []
                             Just tmp -> [tmp]) allcmds
  in drop (length $ head lst) inp

-- This function tries to extract the name of command. In most cases this
-- would be the first word of the string but we have a few exceptions :
-- dg * commands
-- dg-all * commands
-- del * commands
-- del-all * commands
-- add * commands
-- set * commands
-- set-all * commands
getCmdName :: String -> String
getCmdName inp
 = case words inp of
    [] -> []
    wds -> case tail wds of
            []   -> head wds
            lwds -> case head wds of
                     "dg"       -> ("dg "      ++ (head lwds))
                     "dg-all"   -> ("dg-all "  ++ (head lwds))
                     "del"      -> ("del "     ++ (head lwds))
                     "del-all"  -> ("del-all " ++ (head lwds))
                     "add"      -> ("add "     ++ (head lwds))
                     "set"      -> ("set "     ++ (head lwds))
                     "set-all"  -> ("set-all " ++ (head lwds))
                     wd          -> wd

-- | The function determines the requirements of the command
-- name found at the begining of the string
getTypeOf::[CMDL_CmdDescription] -> String -> CMDL_CmdRequirements
getTypeOf allcmds input
 = let nwInput = getCmdName input
       tmp =concatMap(\x ->
                       case find(\y -> y == nwInput )
                                             [cmdName x] of
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
 =
  case getTypeOf allcmds input of
   ReqNodes ->
    case i_state $ intState allState of
     Nothing -> return []
     Just state ->
      do
       -- a pair, where the first element is what needs
       -- to be completed while the second is what is
       -- before the word that needs to be completed
       let (tC,bC) = case isSpace $ lastChar input of
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
                  filter (isPrefixOf tC) allNames
       return res
   ReqGNodes ->
    case i_state $ intState  allState of
     Nothing-> return []
     Just _ ->
      do
        --the last unfinished word that needs to be
        --completed and what is before it
       let (tC,bC) = case isSpace $ lastChar input of
                        -- if last character is a white space
                        -- then there is no word to complete
                         True -> ([], trimRight input)
                        -- otherwise is just the last word
                        -- from the input
                         False -> (lastString $ words input,
                                   unwords $ init
                                   $ words input)
          -- get all goal node names
           allNames = nodeNames (getAllGoalNodes allState)
      -- filter out words that do not start with the word
      -- that needs to be completed
       return $ map(\y -> bC++" "++y) $
           filter(isPrefixOf tC) allNames
   ReqEdges ->
    case i_state $ intState allState of
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
                  filter(isPrefixOf tC) allNames
       return res
   ReqGEdges ->
    case i_state$ intState allState of
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
           lsGE= getAllGoalEdges allState
           allNames = createEdgeNames ls lsGE
          -- filter out words that do not start with the word
          -- that needs to be completed
       return $ map (\y -> bC++" "++y) $
           filter(isPrefixOf tC) allNames
   ReqNodesAndEdges ->
    case i_state $ intState allState of
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
           (tCN,bCN) = case isSpace $ lastChar input of
                         True ->
                          case checkArrowLink $ lastString $ words input of
                           -- we are in the middle of an
                           -- edge, we shouldn't look for
                           -- node names
                           (True,_,_) -> ("Impossible to complete",
                                     [])
                           -- it may be a node
                           _ -> ([], trimRight input)
                         False ->
                          case checkArrowLink $ penultimum $ words input of
                           (True,_,_) -> ("Impossible to complete",
                                    [])
                           _ -> (lastString $ words input,
                                 unwords $ init
                                 $ words input)
           filteredNodes=map (\y -> bCN++" "++y) $
                          filter (isPrefixOf tCN)
                                  $ nodeNames allnodes
           tCE = unfinishedEdgeName $
                     subtractCommandName allcmds input
           bCE = reverse $ trimLeft $ drop (length tCE)
                      $ trimLeft $ reverse input
         -- same as in the ReqEdge case
           edgeNames = createEdgeNames allnodes alledges
           filteredEdges=map (\y -> bCE++" "++y) $
                          filter (isPrefixOf tCE)
                                               edgeNames
      -- sum up the two cases
       return (filteredNodes ++ filteredEdges )
   ReqGNodesAndGEdges ->
    case i_state $ intState allState of
     Nothing -> return []
     Just state ->
      do
       let allnodes = getAllNodes state
           allGE= getAllGoalEdges allState
           penultimum s=lastString $ reverse $ safeTail
                                   $ reverse s
          -- same as in the ReqNode case just that we need
          -- to take care that the word we trying to complete
        -- can also be a node name not only an edge name
           (tCN,bCN) = case isSpace $ lastChar input of
                          True ->
                           case checkArrowLink $ lastString $ words input of
                           -- we are in the middle of an
                           -- edge, we shouldn't look for
                           -- node names
                            (True,_,_) ->("Impossible to complete",
                                     [])
                           --it may be a node
                            _ -> ([], trimRight input)
                          False ->
                           case checkArrowLink $ penultimum $ words input of
                            (True,_,_) ->("Impossible to complete",
                                    [])
                            _ -> (lastString $ words input,
                                  unwords $ init $
                                  words input)
           filteredNodes=map (\y -> bCN++" "++y) $
                          filter(isPrefixOf tCN)
                                $ nodeNames (getAllGoalNodes allState)
           tCE = unfinishedEdgeName $
                     subtractCommandName allcmds input
           bCE = reverse $ trimLeft $ drop (length tCE)
                     $ trimLeft $ reverse input
          -- same as in the ReqEdge case
           edgeNames =createEdgeNames allnodes allGE
           filteredEdges=map (\y -> bCE++" "++y) $
                          filter(isPrefixOf tCE)
                                             edgeNames
          --sum up the two cases
       return (filteredNodes ++ filteredEdges )
   ReqConsCheck ->
      do
       let tC = case isSpace $ lastChar input of
                 True -> []
                 False -> lastString $ words input
           bC = case isSpace $ lastChar input of
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
           getConsCheckersAutomatic' cm = foldl addConsCheckers [] cm
           createConsCheckersList cm = map getPName'
                                         (getConsCheckersAutomatic' cm)
       case  i_state $ intState allState of
        Nothing ->
         -- not in proving mode !? you can not choose a consistency
         -- checker here
               return []
        Just proofState ->
         case cComorphism proofState of
          -- some comorphism was used
          Just c-> return $ map (\y->bC++" "++y) $
                    filter (isPrefixOf tC) $ createConsCheckersList [c]
          Nothing ->
           case elements proofState of
            -- no elements selected
            [] -> return []
            c:_ ->
              case c of
               Element z _ -> return $ map(\y->bC++" "++y)
                               $ filter (isPrefixOf tC)
                               $ createConsCheckersList
                               $ findComorphismPaths
                                 logicGraph
                                   (sublogicOfTh $ theory z)
   ReqProvers ->
      do
       let tC = unwords $ tail $ words input
           bC =  head $ words input
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
           createProverList cm = map getPName' (getProversCMDLautomatic cm)
      -- find the last comorphism used if none use the
      -- the comorphism of the first selected node
       case i_state $ intState allState of
        Nothing ->
       -- not in proving mode !? you can not choose
       -- provers here
                return []
        Just proofState ->
         case cComorphism proofState of
          -- some comorphism was used
          Just c-> do
                    lst <- checkPresenceProvers $ createProverList [c]
                    return $ map (\y -> bC++" "++y) $
                                   filter (isPrefixOf tC) lst
          Nothing ->
           case elements proofState of
             -- no elements selected
             [] -> return []
             -- use the first element to get a comorphism
             c:_ ->
               case c of
                Element z _->do
                              lst <- checkPresenceProvers
                                         $ createProverList
                                         $ findComorphismPaths
                                        logicGraph (sublogicOfTh $ theory z)
                              return $ map (\y -> bC++" "++y)
                                    $ filter (isPrefixOf tC) lst
   ReqComorphism ->
        case i_state $ intState allState of
         Nothing -> return []
         Just pS ->
          case elements pS of
           [] -> return []
           (Element st _):_ ->
              let tC = case isSpace $ lastChar input of
                        True -> []
                        False ->lastString $ words input
                  bC = case isSpace $ lastChar input of
                        True -> trimRight input
                        False-> unwords $ init $ words input
                  cL = concatMap ( \(Comorphism cid) ->
                              case language_name (sourceLogic cid) ==
                                     language_name (logicId st) of
                                False -> []
                                True -> [ language_name cid ]
                             ) comorphismList
              in return $ map (\y -> bC++" "++y)
                        $ filter (isPrefixOf tC) cL
   ReqFile ->
      do
        -- the incomplete path introduced until now
        let initwd = case isSpace $ lastChar input of
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
            bC = case isSpace $ lastChar input of
                  True -> input
                  False -> unwords (init $ words input)
                                 ++ " " ++ tmpPath
        -- leave just folders and files with extenstion .casl
        b' <- doesDirectoryExist lastPath
        ls <- case b' of
               True -> getDirectoryContents lastPath
               False -> return []
        names<- fileFilter lastPath ls []
        -- case list contains only one name
        -- then if it is a folder extend it
        let names' = filter (isPrefixOf tC) names
        names''<- case safeTail names' of
                   -- check CMDL.Utils to see how it
                   -- works, function should be done with
                   -- something like map but that can handle
                   -- functions with IO
                   -- (mapIO !? couldn't make it work though)
                   [] -> fileExtend lastPath names' []
                   _  -> return names'
        return $ map (\y -> bC++y) names''
   ReqAxm ->
      case i_state $ intState allState of
       Nothing-> return []
       Just pS->
        do
         let tC =  case isSpace $ lastChar input of
                    True -> []
                    False-> lastString $ words input
             bC = case isSpace $ lastChar input of
                    True -> trimRight input
                    False -> unwords $ init $ words input
         return $ map(\y-> bC++" "++y) $
          filter (isPrefixOf tC) $ nub $
          concatMap(\(Element st _)->
                 case theory st of
                  G_theory _ _ _ aMap _ ->
                   OMap.keys aMap ) $ elements pS
   ReqGoal ->
      case i_state $ intState allState of
       Nothing-> return []
       Just pS ->
        do
         let tC = case isSpace $ lastChar input of
                   True -> []
                   False -> lastString $ words input
             bC = case isSpace $ lastChar input of
                   True -> trimRight input
                   False-> unwords $ init $ words input
         return $ map (\y->bC++" "++y) $
          filter (isPrefixOf tC) $ nub $
          concatMap(\(Element _ nb)->
                       case getTh Do_translate nb allState of
                        Nothing -> []
                        Just th ->
                          case th of
                           G_theory _ _ _ sens _ ->
                             OMap.keys $
                             OMap.filter
                              (\s -> not (isAxiom s) &&
                               not (isProvenSenStatus s)) sens)
                                     $ elements pS
   ReqNumber -> case words input of
                   [hd] -> return $ map((hd ++ " ") ++)
                                  ["0","1","2","3","4","5","6","7","8","9"]
                   _ : _ : [] -> case isSpace $ lastChar input of
                          True -> return []
                          False ->return $ map(input ++)
                                    ["0","1","2","3","4","5","6","7","8","9"]
                   _ -> return []
   ReqNothing -> return []
   ReqUnknown -> return []
