{- |
Module      :  $Header$
Description :  Manages the history of proof commands
Copyright   :  (c) Markus Gross 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Markus.Gross@dfki.de
Stability   :  provisional
Portability :  portable

Manages the history of proof commands.
-}
module GUI.History (CommandHistory,
                    emptyCommandHistory,
                    initCommandHistory,
                    addToHistUnsafe,
                    addListToHist,
                    addProveToHist,
                    getProofScriptFileName,
                    saveCommandHistory) where

import Common.OrderedMap (keys)
import Common.Utils (splitOn, joinWith)
import Driver.Options (rmSuffix)
import Logic.Comorphism (AnyComorphism(..))
import Logic.Grothendieck (SigId(..))
import Logic.Logic (language_name)
import Proofs.AbstractState
import Static.GTheory (G_theory(..))

import Data.List (isPrefixOf, stripPrefix)
import Data.IORef
import System.Directory(getCurrentDirectory)
import System.IO.Unsafe (unsafePerformIO)

data CommandHistory = CommandHistory {file     :: String,
                                      lastNode :: IORef Int,
                                      hist     :: IORef [String]}

-- Creates an empty command history.
emptyCommandHistory :: IO CommandHistory
emptyCommandHistory =
    do
    ln <- newIORef (-1)
    ch <- newIORef [""]
    return $ CommandHistory {file = "", lastNode = ln, hist = ch}

-- Initializes the command history with a filename.
initCommandHistory :: String -> IO CommandHistory
initCommandHistory f =
    do
    ff <- tryRemoveAbsolutePathComponent f
    let ff' = rmSuffix $ ff
    ln <- newIORef (-1)
    ch <- newIORef ["# automatically generated hets proof-script", "",
                   "use " ++ ff', ""]
    return $ CommandHistory {file = ff', lastNode = ln, hist = ch}

-- Adds a single command to the history.
addToHist :: CommandHistory -> String -> IO ()
addToHist (CommandHistory {hist = ch}) s = 
    readIORef ch >>= (\ch' -> writeIORef ch $ ch' ++ [s])

-- Adds a command to the history and executes a given function.
-- This function is used for the graph menu items.
-- Note: This uses unsafe IO.
addToHistUnsafe :: CommandHistory -> String -> a -> a
addToHistUnsafe ch s a = unsafePerformIO $ addToHist ch s >> return a

-- Adds a list of commands to the history.
addListToHist :: CommandHistory -> [String] -> IO ()
addListToHist _ []     = return ()
addListToHist ch (x:s) = addToHist ch x >> addListToHist ch s

-- Adds a prove to the history.
addProveToHist :: CommandHistory                  -- our history
               -> ProofState lid sentence         -- current proofstate
               -> Maybe (G_prover, AnyComorphism) -- possible used translation
               -> IO ()
addProveToHist ch st acm =
    do
    let nodeName = theoryName st
    let (SigId nodeId) = gTheorySignIdx $ theory st
    ln <- readIORef $ lastNode ch

    -- seperator string and selected node
    if nodeId == ln
        then addToHist ch ""
        else do
             addListToHist ch ["", "# " ++ (take 78 $ repeat '-'), "",
                               "dg basic " ++ (dropName ch nodeName)]
             setLastNode ch nodeId
             return ()

    -- selected prover and translation
    case acm of
        Just (p, c) -> do
                       addToHist ch $ "prover " ++ getProverName p
                       addListToHist ch $ splitComorphism c
        Nothing -> do
                   case selectedProver st of
                       Just s  -> addToHist ch $ "prover " ++ s
                       Nothing -> addToHist ch "# no explicit prover chosen"

    -- selected consistency checker
    case selectedConsChecker st of
        Just s  -> addToHist ch $ "cons-checker " ++ s
        Nothing -> return ()

    -- selected time-limit
    -- for this to work, we have to get into genericATPgui.
    -- this seems very complicated since a lot of non-gui modules use it.

    -- axioms to include in prove
    let allAxioms = case theory st of
                        G_theory _ _ _ axioms _ -> keys axioms
        selAxioms = includedAxioms st
    if allAxioms == selAxioms
       then return ()
       else addToHist ch $ "set axioms " ++ (joinWith ' ' selAxioms)

    -- selected goals and prove command
    let allGoals = keys $ goalMap st
        selGoals = selectedGoals st
    if allGoals == selGoals
        then addToHist ch $ "prove-all"
        else addListToHist ch $ ["set goals " ++
             (joinWith ' ' selGoals), "prove"]

    return ()

-- Saves the history of commands in a file.
saveCommandHistory :: CommandHistory -> String -> IO ()
saveCommandHistory (CommandHistory {hist = c}) f =
    readIORef c >>= (writeFile f . joinWith '\n')

-- Sets the last node.
setLastNode :: CommandHistory -> Int -> IO ()
setLastNode (CommandHistory {lastNode = ln}) nn = writeIORef ln nn

-- Suggests a proof-script filename.
getProofScriptFileName :: CommandHistory -> IO FilePath
getProofScriptFileName (CommandHistory {file = f}) 
    | "/" `isPrefixOf` f = return $ f ++ ".hpf"
    | otherwise          = do
                           dir <- getCurrentDirectory
                           return $ dir ++ "/" ++ f ++ ".hpf"

-- Drops the filename as prefix from a string.
dropName :: CommandHistory -> String -> String
dropName (CommandHistory {file = f}) s = case stripPrefix f s of
                                             Just stripped -> tail stripped
                                             Nothing       -> s

-- Splits the comorphism string into its translations.
splitComorphism :: AnyComorphism -> [String]
splitComorphism (Comorphism cid) = 
    (map ("translate " ++) . tail . splitOn ';') $ language_name cid

-- If an absolute path is given,
-- it tries to remove the current working directory as prefix of it.
tryRemoveAbsolutePathComponent :: String -> IO String
tryRemoveAbsolutePathComponent f 
    | "/" `isPrefixOf` f = do
                           dir <- getCurrentDirectory
                           case stripPrefix (dir ++ "/") f of
                               Just s  -> return s
                               Nothing -> return f
    | otherwise          = return f