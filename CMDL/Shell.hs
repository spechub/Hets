{- |
Module      : ./CMDL/Shell.hs
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
import CMDL.DataTypesUtils

import Common.Utils (trimLeft, trimRight, nubOrd, splitOn)
import Common.Result (Result (Result))

import Comorphisms.LogicGraph (comorphismList, logicGraph,
                               lookupComorphism_in_LG)

import Interfaces.Command (Command (CommentCmd))
import Interfaces.DataTypes
import Interfaces.Utils
import Interfaces.GenericATPState

import Logic.Comorphism
import Logic.Grothendieck (logics, findComorphismPaths,
                           G_sublogics (..))
import Logic.Prover
import Logic.Logic
import Logic.Coerce (coerceSublogic)

import Proofs.AbstractState

import Static.DevGraph
import Static.GTheory

import Data.Char (isSpace)
import Data.List
import qualified Data.Map
import Data.Maybe (mapMaybe, isNothing)
import System.Directory (doesDirectoryExist, getDirectoryContents)

register2history :: CmdlCmdDescription -> CmdlState -> IO CmdlState
register2history dscr state = do
    let oldHistory = i_hist $ intState state
    case undoList oldHistory of
       [] -> return state
       h : r -> case command h of
               CommentCmd _ -> do
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
    -- check the priority of the current command
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
cComment :: String -> CmdlState -> IO CmdlState
cComment _ = return

-- For normal keyboard input

cOpenComment :: String -> CmdlState -> IO CmdlState
cOpenComment _ state = return state { openComment = True }

cCloseComment :: CmdlState -> IO CmdlState
cCloseComment state = return state { openComment = False }

{- | given an input it assumes that it starts with a
   command name and tries to remove this command name -}
subtractCommandName :: [CmdlCmdDescription] -> String -> String
subtractCommandName allcmds input =
  let inp = trimLeft input
  in case mapMaybe ((`stripPrefix` inp) . cmdName) allcmds of
       [] -> inp
       hd : _ -> hd

{- This function tries to extract the name of command. In most cases this
   would be the first word of the string but we have a few exceptions :
   dg * commands
   dg-all * commands
   del * commands
   del-all * commands
   add * commands
   set * commands
   set-all * commands -}
getCmdName :: String -> String
getCmdName inp = case words inp of
    [] -> []
    hw : tws -> case tws of
      [] -> hw
      hwd : _ -> let
        cs = ["dg", "del", "set"]
        csa = "add" : cs ++ map (++ "-all") cs
        in if elem hw csa then hw ++ ' ' : hwd else hw

{- | The function determines the requirements of the command
   name found at the begining of the string -}
getTypeOf :: [CmdlCmdDescription] -> String -> CmdlCmdRequirements
getTypeOf allcmds input
 = let nwInput = getCmdName input
       tmp = concatMap (\ x -> case find (== nwInput) [cmdName x] of
                                Nothing -> []
                                Just _ -> [cmdReq x]) allcmds
   in case tmp of
       result : [] -> result
       _ -> ReqUnknown

nodeNames :: [(a, DGNodeLab)] -> [String]
nodeNames = map (getDGNodeName . snd)

{- | The function provides a list of possible completion
   to a given input if any -}
cmdlCompletionFn :: [CmdlCmdDescription] -> CmdlState -> String -> IO [String]
cmdlCompletionFn allcmds allState input =
   let s0_9 = map show [0 .. (9 :: Int)]
       app h = (h ++) . (' ' :)
   in case getTypeOf allcmds input of
   ReqNodesOrEdges mn mf ->
    case i_state $ intState allState of
     Nothing -> return []
     Just state -> do
       {- a pair, where the first element is what needs
          to be completed while the second is what is
          before the word that needs to be completed
       -}
       let -- get all nodes
           ns = getAllNodes state
           fns = nodeNames $ maybe id (\ f -> filter (\ (_, nd) ->
                     case f of
                       OpenCons -> hasOpenNodeConsStatus False nd
                       OpenGoals -> hasOpenGoals nd))
                     mf ns
           es = map fst
                $ maybe id (\ f -> filter $ case f of
                    OpenCons -> isOpenConsEdge
                    OpenGoals -> edgeContainsGoals
                  . snd) mf
                $ createEdgeNames ns (getAllEdges state)
           allNames = case mn of
             Nothing -> es ++ fns
             Just b -> if b then fns else es
           (fins, tC) = finishedNames allNames
              $ subtractCommandName allcmds input
           -- what is before tC
           bC = reverse $ trimLeft $ drop (length tC) $ reverse input
      {- filter out words that do not start with the word
         that needs to be completed and add the word that
         was before the word that needs to be completed -}
       return $ map (app bC) $ filter (isPrefixOf tC) $ allNames \\ fins
   ReqConsCheck -> do
       let tC = if isSpace $ lastChar input
                 then []
                 else lastString $ words input
           bC = if isSpace $ lastChar input
                 then trimRight input
                 else unwords $ init $ words input
           getCCName (G_cons_checker _ p) = ccName p
           createConsCheckersList = map (getCCName . fst) . getAllConsCheckers
       case i_state $ intState allState of
        Nothing ->
         {- not in proving mode !? you can not choose a consistency
            checker here -}
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
                                   (sublogicOfTheory z)
   ReqProvers -> do
       let bC : tl = words input
           tC = unwords tl
      {- find the last comorphism used if none use the
         the comorphism of the first selected node -}
       case i_state $ intState allState of
        Nothing ->
       {- not in proving mode !? you can not choose
          provers here -}
                return []
        Just proofState ->
           case elements proofState of
             -- no elements selected
             [] -> return []
             -- use the first element to get a comorphism
             c : _ -> case c of
                Element z _ -> do
                  ps <- getUsableProvers ProveCMDLautomatic
                          (sublogicOfTheory z) logicGraph
                  let lst = nub $ map (getProverName . fst) ps
                  return $ map (app bC) $ filter (isPrefixOf tC) lst
   ReqComorphism ->
    let input'' = case words input of
                   cmd : s' -> unwords (cmd : concatMap (splitOn ':')
                                               (concatMap (splitOn ';') s'))
                   _ -> input
        input' = if elem (lastChar input) ";: " then
                   input'' ++ " " else input''
    in case i_state $ intState allState of
         Nothing -> return []
         Just pS ->
          case elements pS of
           [] -> return []
           Element st _ : _ ->
              let tC = if isSpace $ lastChar input'
                        then []
                        else lastString $ words input'
                  appendC' =
                   map (\ coname -> case lookupComorphism_in_LG coname of
                                    Result _ cmor -> cmor) $
                    tail $ words input'
                  appendC = sequence $ (if not (null appendC') &&
                                            isNothing (last appendC')
                                         then init else id) appendC'
                  comor = case appendC of
                           Nothing -> cComorphism pS
                           Just cs ->
                            foldl (\ c1 c2 -> maybe Nothing
                             (`compComorphism` c2) c1)
                             (cComorphism pS) cs
                  bC = if isSpace $ lastChar input'
                        then trimRight input'
                        else unwords $ init $ words input'
                  sl = case comor of
                        Just (Comorphism cid) ->
                         case sublogicOfTheory st of
                          G_sublogics lid sl2 ->
                           case coerceSublogic lid (sourceLogic cid) "" sl2 of
                            Just sl2' -> case mapSublogic cid sl2' of
                             Just sl1 -> G_sublogics (targetLogic cid) sl1
                             Nothing -> G_sublogics (targetLogic cid)
                                          (top_sublogic $ targetLogic cid)
                            Nothing -> G_sublogics (targetLogic cid)
                                        (top_sublogic $ targetLogic cid)
                        Nothing -> sublogicOfTheory st
                  cL = concatMap (\ (Comorphism cid) ->
                                  [ language_name cid
                                    | isSubElemG sl (G_sublogics
                                         (sourceLogic cid)
                                         (sourceSublogic cid)) ]
                                 ) comorphismList
              in return $ map (app bC)
                        $ filter (isPrefixOf tC) cL
   ReqLogic ->
    let l' = lastString $ words input
        i = unwords (init $ words input) ++ " "
    in if elem '.' l'
       then let (l, _ : sl) = Data.List.break (== '.') l'
            in case Data.Map.lookup l $ logics logicGraph of
                Just (Logic lid) -> return $ map ((i ++ l ++ ".") ++) $
                                     filter (Data.List.isPrefixOf sl)
                                     (map sublogicName $ all_sublogics lid)
                Nothing -> return []
       else return $ concatMap
                     (\ (n, Logic lid) ->
                        case map sublogicName $ all_sublogics lid of
                         [_] -> [i ++ n]
                         sls -> (i ++ n) : map
                          (\ sl -> i ++ n ++ "." ++ sl) sls) $
                     filter (Data.List.isPrefixOf l' . fst) $
                     Data.Map.toList $ logics logicGraph
   ReqFile -> do
        -- the incomplete path introduced until now
        let initwd = if isSpace $ lastChar input
                      then []
                      else lastString $ words input
        {- the folder in which to look for (it might be
           empty) -}
            tmpPath = reverse $ dropWhile (/= '/') $ reverse initwd
        {- in case no folder was introduced yet look into
           current folder -}
            lastPath = case tmpPath of
                       [] -> "./"
                       _ -> tmpPath
        {- the name of file/directory that needs to be
           completed from the already introduced path -}
            tC = reverse $ takeWhile (/= '/') $ reverse initwd
            bC = if isSpace $ lastChar input
                  then input
                  else unwords (init $ words input) ++ " " ++ tmpPath
        -- leave just folders and files with extenstion .casl
        b' <- doesDirectoryExist lastPath
        ls <- if b' then getDirectoryContents lastPath else return []
        names <- fileFilter lastPath ls []
        {- case list contains only one name
           then if it is a folder extend it -}
        let names' = filter (isPrefixOf tC) names
        names'' <- case safeTail names' of
                   {- check CMDL.Utils to see how it
                      works, function should be done with
                      something like map but that can handle
                      functions with IO
                      (mapIO !? couldn't make it work though) -}
                   [] -> fileExtend lastPath names' []
                   _ -> return names'
        return $ map (bC ++) names''
   ReqAxm b ->
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
         return $ map (app bC) $ filter (isPrefixOf tC) $ nubOrd
           $ concatMap (\ (Element st nb) ->
               if b then map fst $ getAxioms st else
                        case getTh Do_translate nb allState of
                        Nothing -> []
                        Just th -> map fst $ filter
                            (maybe False (not . isProvedBasically) . snd)
                            $ getThGoals th)
                $ elements pS
   ReqNumber -> case words input of
                   [hd] -> return $ map (app hd) s0_9
                   _ : _ : [] -> return $ if isSpace $ lastChar input
                          then []
                          else map (input ++) s0_9
                   _ -> return []
   ReqNothing -> return []
   ReqUnknown -> return []
