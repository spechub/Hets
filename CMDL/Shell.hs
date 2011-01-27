{- |
Module      : $Header$
Description : shell related functions
Copyright   : uni-bremen and DFKI
License     : GPLv2 or higher, see LICENSE.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

CMDL.Shell contains almost all functions related
the CMDL shell or haskeline
-}

module CMDL.Shell
       ( cComment
       , cOpenComment
       , cCloseComment
       , nodeNames
       , cmdlCompletionFn
       , checkCom
       ) where

import CMDL.DataTypes
import CMDL.Utils
import CMDL.DataTypesUtils(getAllNodes, getAllGoalEdges, getAllGoalNodes, getTh)

import Common.AS_Annotation(SenAttr(isAxiom))
import Common.Utils(trimLeft, trimRight)
import qualified Common.OrderedMap as OMap

import Comorphisms.LogicGraph(comorphismList, logicGraph)

import Interfaces.Command(Command(CommentCmd))
import Interfaces.DataTypes
import Interfaces.Utils(getAllEdges)
import Interfaces.GenericATPState

import Logic.Comorphism
import Logic.Grothendieck(findComorphismPaths)
import Logic.Prover
import Logic.Logic

import Proofs.AbstractState

import Static.DevGraph
import Static.GTheory

import Data.Char(isSpace)
import Data.List
import System.Directory(doesDirectoryExist, getDirectoryContents)

register2history :: CmdlCmdDescription -> CmdlState -> IO CmdlState
register2history dscr state = do
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
processComment :: CmdlState -> String -> CmdlState
processComment st inp =
  if isInfixOf "}%" inp then st { openComment = False } else st

-- adds a line to the script
addToScript :: CmdlState -> IntIState -> String -> CmdlState
addToScript st ist str
 = let olds = script ist
       oldextOpts = tsExtraOpts olds
   in st {
        intState = (intState st) {
                     i_state = Just ist {
                       script = olds { tsExtraOpts = str : oldextOpts } }
          } }

checkCom :: CmdlCmdDescription -> CmdlState -> IO CmdlState
checkCom descr state =
    --check the priority of the current command
    case cmdPriority descr of
     CmdNoPriority ->
      -- check if there is open comment
      if openComment state
       then return $ processComment state $ cmdInput descr
       else
        case i_state $ intState state of
         Nothing -> register2history descr state
         Just ist ->
          -- check if there is inside a script
          if loadScript ist
            then return $ addToScript state ist
                        $ cmdName descr ++ " " ++ cmdInput descr
            else register2history descr state
     CmdGreaterThanComments ->
      case i_state $ intState state of
       Nothing -> register2history descr state
       Just ist ->
        if loadScript ist
          then return $ addToScript state ist
                      $ cmdName descr ++ " " ++ cmdInput descr
          else register2history descr state
     CmdGreaterThanScriptAndComments -> return state

-- | Function handle a comment line
cComment::String -> CmdlState -> IO CmdlState
cComment _ = return

-- For normal keyboard input

cOpenComment :: String -> CmdlState -> IO CmdlState
cOpenComment _ state = return state { openComment = True }

cCloseComment :: CmdlState -> IO CmdlState
cCloseComment state = return state { openComment = False }

-- | given an input it assumes that it starts with a
-- command name and tries to remove this command name
subtractCommandName::[CmdlCmdDescription] -> String -> String
subtractCommandName allcmds input =
  let inp = trimLeft input
      lst = concatMap(\ x -> case find (flip isPrefixOf inp) [cmdName x] of
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
getCmdName inp = case words inp of
    [] -> []
    hw : tws -> case tws of
      [] -> hw
      hwd : _ -> let
        cs = ["dg", "del", "set"]
        csa = "add" : cs ++ map (++ "-all") cs
        in if elem hw csa then hw ++ ' ' : hwd else hw

-- | The function determines the requirements of the command
-- name found at the begining of the string
getTypeOf::[CmdlCmdDescription] -> String -> CmdlCmdRequirements
getTypeOf allcmds input
 = let nwInput = getCmdName input
       tmp = concatMap(\ x -> case find (== nwInput) [cmdName x] of
                                Nothing -> []
                                Just _ -> [cmdReq x]) allcmds
   in case tmp of
       result : [] -> result
       _ -> ReqUnknown

nodeNames :: [(a, DGNodeLab)] -> [String]
nodeNames = map (showName . dgn_name . snd)

-- | The function provides a list of possible completion
-- to a given input if any
cmdlCompletionFn :: [CmdlCmdDescription] -> CmdlState -> String -> IO [String]
cmdlCompletionFn allcmds allState input =
   let s0_9 = map show [0 .. (9 :: Int)]
       app h = (h ++) . (' ' :)
   in case getTypeOf allcmds input of
   ReqNodes ->
    case i_state $ intState allState of
     Nothing -> return []
     Just state -> do
       -- a pair, where the first element is what needs
       -- to be completed while the second is what is
       -- before the word that needs to be completed
       let (tC,bC) = if isSpace $ lastChar input
                        -- if last character is a white space
                        -- then there is no word to complete
                         then ([], trimRight input)
                        -- otherwise is just the last word
                        -- from the input
                         else (lastString $ words input,
                               unwords $ init $ words input)
          -- get all node names
           allNames = nodeNames (getAllNodes state)
      -- filter out words that do not start with the word
      -- that needs to be completed and add the word that
      -- was before the word that needs to be completed
       let res = map (app bC) $ filter (isPrefixOf tC) allNames
       return res
   ReqGNodes ->
    case i_state $ intState  allState of
     Nothing -> return []
     Just _ -> do
        --the last unfinished word that needs to be
        --completed and what is before it
       let (tC,bC) = if isSpace $ lastChar input
                        -- if last character is a white space
                        -- then there is no word to complete
                         then ([], trimRight input)
                        -- otherwise is just the last word
                        -- from the input
                         else (lastString $ words input,
                               unwords $ init $ words input)
          -- get all goal node names
           allNames = nodeNames (getAllGoalNodes allState)
      -- filter out words that do not start with the word
      -- that needs to be completed
       return $ map(app bC) $ filter(isPrefixOf tC) allNames
   ReqEdges ->
    case i_state $ intState allState of
     Nothing -> return []
     Just state -> do
      --the last unfinished edge name that needs to be
      --completed
       let tC = unfinishedEdgeName $ subtractCommandName allcmds input
          -- what is before this list
           bC = reverse $ trimLeft $ drop (length tC)
                     $ trimLeft $ reverse input
          -- get all nodes
           ls = getAllNodes state
          -- get all edges
           lsE = getAllEdges state
          -- get all edge names
           allNames = createEdgeNames ls lsE
      -- filter out words that do not start with the word
      -- that needs to be completed
       let res = map (app bC) $ filter(isPrefixOf tC) allNames
       return res
   ReqGEdges ->
    case i_state $ intState allState of
     Nothing -> return []
     Just state ->
      do
      -- the last unfinished edge name that needs to be
      -- completed
       let tC = unfinishedEdgeName $ subtractCommandName allcmds input
           bC = reverse $ trimLeft $ drop (length tC)
                     $ trimLeft $ reverse input
           ls  = getAllNodes state
           lsGE= getAllGoalEdges allState
           allNames = createEdgeNames ls lsGE
          -- filter out words that do not start with the word
          -- that needs to be completed
       return $ map (app bC) $ filter(isPrefixOf tC) allNames
   ReqConsCheck -> do
       let tC = if isSpace $ lastChar input
                 then []
                 else lastString $ words input
           bC = if isSpace $ lastChar input
                 then trimRight input
                 else unwords $ init $ words input
           getCCName (G_cons_checker _ p) = ccName p
           createConsCheckersList = map (getCCName . fst) . getConsCheckers
       case i_state $ intState allState of
        Nothing ->
         -- not in proving mode !? you can not choose a consistency
         -- checker here
               return []
        Just proofState ->
         case cComorphism proofState of
          -- some comorphism was used
          Just c -> return $ map (app bC) $ filter (isPrefixOf tC)
                   $ createConsCheckersList [c]
          Nothing ->
           case elements proofState of
            -- no elements selected
            [] -> return []
            c : _ -> case c of
               Element z _ -> return $ map (app bC)
                               $ filter (isPrefixOf tC)
                               $ createConsCheckersList
                               $ findComorphismPaths logicGraph
                                   (sublogicOfTh $ theory z)
   ReqProvers -> do
       let bC : tl = words input
           tC = unwords tl
      -- find the last comorphism used if none use the
      -- the comorphism of the first selected node
       case i_state $ intState allState of
        Nothing ->
       -- not in proving mode !? you can not choose
       -- provers here
                return []
        Just proofState ->
           case elements proofState of
             -- no elements selected
             [] -> return []
             -- use the first element to get a comorphism
             c : _ -> case c of
                Element z _ -> do
                  let proverList =
                        map (getProverName . fst)
                        $ case cComorphism proofState of
                          Nothing -> id
                          Just com -> filter ((== com) . snd)
                        $ getAllProvers ProveCMDLautomatic
                          (sublogicOfTh $ theory z) logicGraph
                  lst <- checkPresenceProvers proverList
                  return $ map (app bC) $ filter (isPrefixOf tC) lst
   ReqComorphism ->
        case i_state $ intState allState of
         Nothing -> return []
         Just pS ->
          case elements pS of
           [] -> return []
           Element st _ : _ ->
              let tC = if isSpace $ lastChar input
                        then []
                        else lastString $ words input
                  bC = if isSpace $ lastChar input
                        then trimRight input
                        else unwords $ init $ words input
                  cL = concatMap (\ (Comorphism cid) ->
                                  [ language_name cid
                                    | language_name (sourceLogic cid) ==
                                      logicId st ]
                                 ) comorphismList
              in return $ map (app bC)
                        $ filter (isPrefixOf tC) cL
   ReqFile -> do
        -- the incomplete path introduced until now
        let initwd = if isSpace $ lastChar input
                      then []
                      else lastString $ words input
        -- the folder in which to look for (it might be
        -- empty)
            tmpPath=reverse $ dropWhile (/= '/') $ reverse initwd
        -- in case no folder was introduced yet look into
        -- current folder
            lastPath = case tmpPath of
                       [] -> "./"
                       _  -> tmpPath
        -- the name of file/directory that needs to be
        -- completed from the already introduced path
            tC=reverse $ takeWhile (/= '/') $ reverse initwd
            bC = if isSpace $ lastChar input
                  then input
                  else unwords (init $ words input) ++ " " ++ tmpPath
        -- leave just folders and files with extenstion .casl
        b' <- doesDirectoryExist lastPath
        ls <- if b' then getDirectoryContents lastPath else return []
        names <- fileFilter lastPath ls []
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
        return $ map (bC ++) names''
   ReqAxm ->
      case i_state $ intState allState of
       Nothing -> return []
       Just pS ->
        do
         let tC =  if isSpace $ lastChar input
                    then []
                    else lastString $ words input
             bC = if isSpace $ lastChar input
                    then trimRight input
                    else unwords $ init $ words input
         return $ map(app bC) $ filter (isPrefixOf tC) $ nub
           $ concatMap(\ (Element st _) ->
                 case theory st of
                  G_theory _ _ _ aMap _ -> OMap.keys aMap ) $ elements pS
   ReqGoal ->
      case i_state $ intState allState of
       Nothing -> return []
       Just pS ->
        do
         let tC = if isSpace $ lastChar input
                   then []
                   else lastString $ words input
             bC = if isSpace $ lastChar input
                   then trimRight input
                   else unwords $ init $ words input
         return $ map (app bC) $ filter (isPrefixOf tC) $ nub
           $ concatMap(\ (Element _ nb)->
                       case getTh Do_translate nb allState of
                        Nothing -> []
                        Just th ->
                          case th of
                           G_theory _ _ _ sens _ ->
                             OMap.keys $ OMap.filter
                              (\ s -> not (isAxiom s) &&
                               not (isProvenSenStatus s)) sens)
                                     $ elements pS
   ReqNumber -> case words input of
                   [hd] -> return $ map(app hd) s0_9
                   _ : _ : [] -> if isSpace $ lastChar input
                          then return []
                          else return $ map (input ++) s0_9
                   _ -> return []
   ReqNothing -> return []
   ReqUnknown -> return []
