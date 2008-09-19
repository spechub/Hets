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
                    addMenuItemToHist,
                    addListToHist,
                    checkAndAddProve,
                    getProofScriptFileName,
                    saveCommandHistory) where

import Common.OrderedMap (keys)
import Common.Utils (joinWith, splitOn)
import Driver.Options (rmSuffix)
import Logic.Comorphism (AnyComorphism(..))
import Logic.Grothendieck (SigId(..))
import Logic.Logic (language_name)
import Logic.Prover
import Proofs.AbstractState
import Static.GTheory (G_theory(..))

import Data.List (isPrefixOf, stripPrefix)
import Data.IORef
import System.Directory (getCurrentDirectory)

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
addToHist ch s = addListToHist ch [s]

-- Adds a list of commands to the history.
addListToHist :: CommandHistory -> [String] -> IO ()
addListToHist (CommandHistory {hist = c}) l =
    readIORef c >>= (\c' -> writeIORef c $ c' ++ l)

-- Adds a menu item to the history.
addMenuItemToHist :: CommandHistory -> String -> IO ()
addMenuItemToHist ch item = case lookup item menuItems of
                                Just s  -> addToHist ch s
                                Nothing -> return ()

-- A List of menu items and their corresponding proof-script command.
menuItems :: [(String, String)]
menuItems = [
    ("Automatic", "dg-all auto"),
    ("Global Subsumption", "dg-all glob-subsume"),
    ("Global Decomposition", "dg-all glob-decomp"),
    ("Local Inference", "dg-all loc-infer"),
    ("Local Decomposition (merge of rules)", "dg-all loc-decomp"),
    ("Composition (merge of rules)", "dg-all comp"),
    ("Composition - creating new links", "dg-all comp-new"),
    ("Hide Theorem Shift", "dg-all hide-thm"),
    ("Theorem Hide Shift", "dg-all thm-hide")
    ]

-- If at least one goal was proved the prove gets added, otherwise not.
checkAndAddProve :: (Eq proof_tree) => CommandHistory
        -> ProofState lid sentence -- current proofstate
        -> Maybe (G_prover, AnyComorphism) -- possible used translation
        -> [Proof_status proof_tree] -- goals included in prove
        -> IO ()
checkAndAddProve ch st pcm pt
    | goals == [] = return ()
    | otherwise   = addProveToHist ch st pcm goals
    where
        -- 1. filter out the not proven goals
        -- 2. reverse the list, because the last proven goals are on top
        goals = reverse $ filter (wasProved) pt
        -- This checks wether a goal was proved or not.
        wasProved :: Proof_status proof_tree -> Bool
        wasProved g = case goalStatus g of
                          Proved _ -> True
                          _        -> False

-- Adds a prove to the history.
addProveToHist :: CommandHistory
    -> ProofState lid sentence -- current proofstate
    -> Maybe (G_prover, AnyComorphism) -- possible used translation
    -> [Proof_status proof_tree] -- proven goals included in prove
    -> IO ()
addProveToHist ch st pcm goals =
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

    -- selected translations
    case pcm of
        Just (_, cm) -> do addListToHist ch ("drop-translations" : 
                                             splitComorphism cm)
                           addToHist ch ""
        Nothing      -> return ()
    
    -- process each goal
    mapM_ (addGoalToHist ch st pcm) goals

    return ()

-- Adds a prove for a goal to the history.
addGoalToHist :: CommandHistory
    -> ProofState lid sentence -- current proofstate
    -> Maybe (G_prover, AnyComorphism) -- possible used translation
    -> Proof_status proof_tree -- current goal
    -> IO ()
addGoalToHist ch st pcm g =
    do
    addToHist ch $ "set goals " ++ (goalName g)

    -- axioms to include in prove
    let allAxioms = case theory st of
                        G_theory _ _ _ axioms _ -> keys axioms
        selAxioms = usedAxioms g
    if allAxioms == selAxioms || selAxioms == []
       then addToHist ch $ "set-all axioms"
       else addToHist ch $ "set axioms " ++ (joinWith ' ' selAxioms)

    -- selected time-limit
    let (Tactic_script s) = tacticScript g
    case parseTimeLimit $ splitOn '\n' s of
        Just timeLimit -> addToHist ch $ "set time-limit " ++ timeLimit
        Nothing        -> return ()

    -- selected prover
    case pcm of
        Just (p, _) -> addToHist ch $ "prover " ++ getProverName p
        Nothing     -> do
                       case selectedProver st of
                           Just sp -> addToHist ch $ "prover " ++ sp
                           Nothing -> addToHist ch "# no explicit prover chosen"
    addListToHist ch ["prove", ""]

    return ()

-- Parses time-limit from the tactic-script of a goal.
parseTimeLimit :: [String] -> Maybe String
parseTimeLimit l = case length l' of
                       1 -> Just (drop (length "Time limit: ") $ head l')
                       _ -> Nothing
                   where
                       l' = filter (isPrefixOf "Time limit: ") l

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
