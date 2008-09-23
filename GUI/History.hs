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

-- This datastructure holds all information for the history.
data CommandHistory = CommandHistory {file      :: String,
                                      lastNode  :: IORef Int,
                                      lastProve :: IORef Prove,
                                      hist      :: IORef [String]}

-- This represents a prove with all properties needed to add it to the history.
data Prove = Prove {nodeId :: Int, -- id of the node
                    nodeName :: String, -- name of the node
                    prover :: Maybe String, -- name of the prover
                    translation :: Maybe AnyComorphism,  -- used translation
                    timeLimit :: Int, -- chosen time-limit
                    provenGoals :: [ProvenGoal], -- proven goals
                    allAxioms :: [String] -- all available axioms
                   } deriving Eq

-- This represents the information about a proved goal
data ProvenGoal = ProvenGoal {name :: String, -- name of the goal
                              axioms :: [String] -- used axioms in the prove
                             } deriving Eq

-- Creates an empty command history.
emptyCommandHistory :: IO CommandHistory
emptyCommandHistory =
    do
    ln <- newIORef (-1)
    lp <- newIORef emptyProve
    ch <- newIORef [""]
    return $ CommandHistory{file = "", lastNode = ln, lastProve = lp, hist = ch}

-- Initializes the command history with a filename.
initCommandHistory :: String -> IO CommandHistory
initCommandHistory f =
    do
    eh <- emptyCommandHistory
    ff <- tryRemoveAbsolutePathComponent f
    let ff' = rmSuffix ff
    ch <- newIORef ["# automatically generated hets proof-script", "",
                   "use " ++ ff', ""]
    return $ eh {file = ff', hist = ch}

-- Creates an empty prove.
emptyProve :: Prove
emptyProve = Prove {nodeId = -1,
                    nodeName = "",
                    prover = Nothing,
                    translation = Nothing,
                    timeLimit = -1,
                    provenGoals = [],
                    allAxioms = []}

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

-- If at least one goal was proved and the prove is not the same as last-time
-- the prove gets added, otherwise not.
checkAndAddProve :: (Eq proof_tree) => CommandHistory
        -> ProofState lid sentence -- current proofstate
        -> Maybe (G_prover, AnyComorphism) -- possible used translation
        -> [Proof_status proof_tree] -- goals included in prove
        -> IO ()
checkAndAddProve ch st pcm pt
    | goals == [] = return ()
    | otherwise   = do
                    prove <- convertProofTreeToProve st pcm goals
                    lp <- readIORef $ lastProve ch
                    if prove == lp
                        then return()
                        else do
                             setLastProve ch prove
                             addProveToHist ch (prove{provenGoals = mergeGoals $
                                                             provenGoals prove})
    where
        -- 1. filter out the not proven goals
        -- 2. reverse the list, because the last proven goals are on top
        goals = reverse $ filter (wasProved) pt
        -- This checks wether a goal was proved or not.
        wasProved :: Proof_status proof_tree -> Bool
        wasProved g = case goalStatus g of
                          Proved _ -> True
                          _        -> False

-- Converts a list of proof-trees to a prove.
convertProofTreeToProve :: (Eq proof_tree) =>
       ProofState lid sentence -- current proofstate
    -> Maybe (G_prover, AnyComorphism) -- possible used translation
    -> [Proof_status proof_tree] -- goals included in prove
    -> IO Prove
convertProofTreeToProve st pcm goals =
    do
    -- selected node
    let nname = theoryName st
    let (SigId nId) = gTheorySignIdx $ theory st

    -- selected time-limit
    let (Tactic_script script) = tacticScript (head goals)
    let tlimit = case parseTimeLimit $ splitOn '\n' script of
                     Just limit -> read limit
                     Nothing    -> 20

    -- selected prover
    let prvr = case pcm of
                     Just (p, _) -> Just (getProverName p)
                     Nothing     -> selectedProver st

    -- selected translation
    let trans = case pcm of
                    Just (_, cm) -> Just cm
                    Nothing      -> Nothing

    -- convert all proof-trees to goals
    let convertedGoals = map (convertGoal) goals

    -- axioms to include in prove
    let allax = case theory st of
                     G_theory _ _ _ axs _ -> keys axs

    return $ Prove {nodeId = nId,
                    nodeName = nname,
                    prover = prvr,
                    translation = trans,
                    timeLimit = tlimit,
                    provenGoals = convertedGoals,
                    allAxioms = allax}

-- Converts a proof-tree into a goal.
convertGoal :: Proof_status proof_tree -> ProvenGoal
convertGoal pt = ProvenGoal {name = goalName pt,
                             axioms = usedAxioms pt}

-- Merges goals with the same used axioms into one goal.
mergeGoals :: [ProvenGoal] -> [ProvenGoal]
mergeGoals []     = []
mergeGoals (h:[]) = [h]
mergeGoals (h:t)  | axioms h == axioms h' = mergeGoals $ (merge h h'):(tail t)
                  | otherwise             = h:(mergeGoals t)
                  where
                      h' = head t
                      merge :: ProvenGoal -> ProvenGoal -> ProvenGoal
                      merge a b = a {name = name a ++ ' ':(name b)}

-- Adds a prove to the history.
addProveToHist :: CommandHistory -> Prove -> IO ()
addProveToHist ch p =
    do
    ln <- readIORef $ lastNode ch

    -- seperator string and selected node
    if nodeId p == ln
        then addToHist ch ""
        else do
             addListToHist ch ["", "# " ++ (take 78 $ repeat '-'), "",
                               "dg basic " ++ (dropName ch $ nodeName p)]
             setLastNode ch $ nodeId p
             return ()

    -- selected translations
    addToHist ch "drop-translations"
    case translation p of
        Just acm -> addListToHist ch $ splitComorphism acm
        Nothing  -> return ()

    -- selected prover
    case prover p of
        Just prvr -> addToHist ch $ "prover " ++ prvr
        Nothing   -> addToHist ch "# no explicit prover chosen"
    addToHist ch ""

    -- process each goal
    mapM_ (addGoalToHist ch p) $ provenGoals p

    return ()

-- Adds a prove for a goal to the history.
addGoalToHist :: CommandHistory -> Prove -> ProvenGoal -> IO ()
addGoalToHist ch p g =
    do
    addToHist ch $ "set goals " ++ (name g)

    -- axioms to include in prove
    if (allAxioms p) == (axioms g) || (axioms g) == []
       then addToHist ch $ "set-all axioms"
       else addToHist ch $ "set axioms " ++ (joinWith ' ' $ axioms g)

    -- selected time-limit
    addToHist ch $ "set time-limit " ++ (show $ timeLimit p)

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
setLastNode (CommandHistory {lastNode = ln}) = writeIORef ln

-- Sets the last prove.
setLastProve :: CommandHistory -> Prove -> IO ()
setLastProve (CommandHistory {lastProve = lp}) = writeIORef lp

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
