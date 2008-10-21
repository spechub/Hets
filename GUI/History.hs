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
                    addProveToHist,
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

import Control.Monad (when)
import Data.IORef
import Data.List (isPrefixOf, stripPrefix)
import Data.Maybe (fromMaybe)
import System.Directory (getCurrentDirectory)

-- This datastructure holds all information for the history.
data CommandHistory = CommandHistory {file :: String,
                                      hist :: IORef [Command]}

-- Represents a command in the history.
data Command = DGComm DGCommand | NodeChange Node | ProveCommand Prove
               deriving Eq

instance Show Command where
    show (DGComm c)       = show c
    show (NodeChange n)   = show n
    show (ProveCommand p) = show p

-- This is used to recognize a change of node between the proofs.
data Node = Node Int String deriving Eq

instance Show Node where
    show (Node _ nName) =
        "\n# " ++ (replicate 78 '-') ++ "\n\ndg basic " ++ nName ++ "\n"

-- This represents a dg menu-item.
data DGCommand = AllAuto      | AllGlobSubsume | AllGlobDecomp | AllLocInfer |
                 AllLocDecomp | AllComp        | AllCompNew    | AllHideThm  |
                 AllThmHide   deriving Eq

instance Show DGCommand where
    show AllAuto        = "dg-all auto"
    show AllGlobSubsume = "dg-all glob-subsume"
    show AllGlobDecomp  = "dg-all glob-decomp"
    show AllLocInfer    = "dg-all loc-infer"
    show AllLocDecomp   = "dg-all loc-decomp"
    show AllComp        = "dg-all comp"
    show AllCompNew     = "dg-all comp-new"
    show AllHideThm     = "dg-all hide-thm"
    show AllThmHide     = "dg-all thm-hide"

-- This represents a prove with all properties needed to add it to the history.
data Prove = Prove {prover      :: Maybe String,        -- name of the prover
                    translation :: Maybe AnyComorphism, -- used translation
                    provenGoals :: [ProvenGoal],        -- proven goals
                    allAxioms   :: [String]             -- all available axioms
                   } deriving Eq

instance Show Prove where
    show p =
        "drop-translations\n"
        ++
        -- selected translation
        (maybe "" (unlines . splitComorphism) $ translation p)
        ++
        -- selected prover
        (maybe "# no prover chosen" ("prover " ++) $ prover p) ++ "\n\n"
        ++
        -- proven goals
        (unlines $ map (goalToString p) $ provenGoals p)

-- This represents the information about a proved goal
data ProvenGoal = ProvenGoal {name      :: String,   -- name of the goal
                              axioms    :: [String], -- used axioms in the prove
                              timeLimit :: Int       -- chosen time-limit
                             } deriving Eq

-- Converts a proven goal to a string.
goalToString :: Prove -> ProvenGoal -> String
goalToString p g =
    "set goals " ++ (name g)
    ++
    -- axioms to include in prove
    '\n':(if (allAxioms p == axioms g) || (null $ axioms g)
              then "set-all axioms"
              else "set axioms " ++ (joinWith ' ' $ axioms g))
    ++
    -- selected time-limit
    "\nset time-limit " ++ (show $ timeLimit g) ++ "\nprove\n"

-- Creates an empty command history.
emptyCommandHistory :: IO CommandHistory
emptyCommandHistory = initCommandHistory ""

-- Initializes the command history with a filename.
initCommandHistory :: String -> IO CommandHistory
initCommandHistory f =
    do
    ff <- tryRemoveAbsolutePathComponent f
    ch <- newIORef []
    return $ CommandHistory {file = rmSuffix ff, hist = ch}

-- Adds a single command to the history.
addToHist :: CommandHistory -> Command -> IO ()
addToHist (CommandHistory {hist = c}) cm =
    readIORef c >>= (\h -> writeIORef c $ h ++ [cm])

-- Adds a menu item to the history.
addMenuItemToHist :: CommandHistory -> String -> IO ()
addMenuItemToHist ch item =
    maybe (return ()) (addToHist ch . DGComm) (lookup item menuItems)

-- A List of menu items and their corresponding proof-script command.
menuItems :: [(String, DGCommand)]
menuItems = [
    ("Automatic",                            AllAuto),
    ("Global Subsumption",                   AllGlobSubsume),
    ("Global Decomposition",                 AllGlobDecomp),
    ("Local Inference",                      AllLocInfer),
    ("Local Decomposition (merge of rules)", AllLocDecomp),
    ("Composition (merge of rules)",         AllComp),
    ("Composition - creating new links",     AllCompNew),
    ("Hide Theorem Shift",                   AllHideThm),
    ("Theorem Hide Shift",                   AllThmHide)
    ]

-- If at least one goal was proved and the prove is not the same as last time
-- the prove gets added, otherwise not.
addProveToHist :: CommandHistory
        -> ProofState lid sentence         -- current proofstate
        -> Maybe (G_prover, AnyComorphism) -- possible used translation
        -> [Proof_status proof_tree]       -- goals included in prove
        -> IO ()
addProveToHist ch st pcm pt
    | null $ filter (wasProved) pt = return ()
    | otherwise = do
                  p' <- proofTreeToProve st pcm pt
                  mp <- getLastProve ch
                  case mp of
                      Just p  -> when (p /= p') (addProve p')
                      Nothing -> addProve p'
    where
        -- Drops the filename as prefix from a node-name.
        dropName :: String -> String
        dropName s = maybe s (tail) (stripPrefix (file ch) s)
        -- Adds a prove to the history.
        addProve :: Prove -> IO ()
        addProve p =
            do
            -- Create new NodeChange and compare it with last found NodeChange.
            let (SigId nId) = gTheorySignIdx $ theory st
            let nc' = NodeChange $ Node nId (dropName $ theoryName st)
            mn <- getLastNode ch
            -- Add new NodeChange if it doesn't match.
            case mn of
                Just n  -> when (NodeChange n /= nc') (addToHist ch nc')
                Nothing -> addToHist ch nc'
            -- Finally add the prove.
            addToHist ch $ ProveCommand p

-- Converts a list of proof-trees to a prove.
proofTreeToProve :: ProofState lid sentence -- current proofstate
    -> Maybe (G_prover, AnyComorphism)      -- possible used translation
    -> [Proof_status proof_tree]            -- goals included in prove
    -> IO Prove
proofTreeToProve st pcm pt =
    do
    -- selected prover
    let prvr = maybe (selectedProver st) (Just . getProverName . fst) pcm
    -- selected translation
    let trans = maybe Nothing (Just . snd) pcm
    -- 1. filter out the not proven goals
    -- 2. reverse the list, because the last proven goals are on top
    -- 3. convert all proof-trees to goals
    -- 4. merge goals with same used axioms
    let goals = mergeGoals $ reverse $ map (convertGoal) $ filter (wasProved) pt
    -- axioms to include in prove
    let allax = case theory st of
                    G_theory _ _ _ axs _ -> keys axs
    return $ Prove {prover = prvr,
                    translation = trans,
                    provenGoals = goals,
                    allAxioms = allax}

-- This checks wether a goal was proved or not.
wasProved :: Proof_status proof_tree -> Bool
wasProved g = case goalStatus g of
    Proved _ -> True
    _        -> False

-- Converts a proof-tree into a goal.
convertGoal :: Proof_status proof_tree -> ProvenGoal
convertGoal pt =
    ProvenGoal {name = goalName pt, axioms = usedAxioms pt, timeLimit = tlimit}
    where
        (Tactic_script script) = tacticScript pt
        tlimit = maybe 20 (read) (parseTimeLimit $ splitOn '\n' script)

-- Parses time-limit from the tactic-script of a goal.
parseTimeLimit :: [String] -> Maybe String
parseTimeLimit l =
    if null l' then Nothing else Just $ drop (length tlStr) $ last l'
    where
        l' = filter (isPrefixOf tlStr) l
        tlStr = "Time limit: "

-- Merges goals with the same used axioms into one goal.
mergeGoals :: [ProvenGoal] -> [ProvenGoal]
mergeGoals []     = []
mergeGoals (h:[]) = [h]
mergeGoals (h:t)  | mergeAble h h' = mergeGoals $ (merge h h'):(tail t)
                  | otherwise      = h:(mergeGoals t)
                  where
                      h' = head t
                      mergeAble :: ProvenGoal -> ProvenGoal -> Bool
                      mergeAble a b = axioms a == axioms b &&
                                      timeLimit a == timeLimit b
                      merge :: ProvenGoal -> ProvenGoal -> ProvenGoal
                      merge a b = a{name = name a ++ ' ':(name b)}

-- Returns the last nodechange in the history.
getLastNode :: CommandHistory -> IO (Maybe Node)
getLastNode (CommandHistory{hist = c}) =
    do
    h <- readIORef c
    let h' = [n | NodeChange n <- h]
    return $ if null h' then Nothing else Just $ last h'

-- If the last command in history is a prove it gets returned.
getLastProve :: CommandHistory -> IO (Maybe Prove)
getLastProve (CommandHistory{hist = c}) =
    do
    h <- readIORef c
    return $ if null h
               then Nothing
               else case last h of
                        ProveCommand p -> Just p
                        _              -> Nothing

-- Saves the history of commands in a file.
saveCommandHistory :: CommandHistory -> String -> IO ()
saveCommandHistory (CommandHistory {file = ff, hist = c}) f =
    do
    h <- readIORef c
    let history = ["# automatically generated hets proof-script", "",
                   "use " ++ ff, ""] ++ map (show) h
    writeFile f $ joinWith '\n' history

-- Suggests a proof-script filename.
getProofScriptFileName :: CommandHistory -> IO FilePath
getProofScriptFileName (CommandHistory {file = f})
    | "/" `isPrefixOf` f = return $ f ++ ".hpf"
    | otherwise          = do
                           dir <- getCurrentDirectory
                           return $ dir ++ '/':f ++ ".hpf"

-- Splits the comorphism string into its translations.
splitComorphism :: AnyComorphism -> [String]
splitComorphism (Comorphism cid) =
    map ("translate " ++) $ tail $ splitOn ';' $ language_name cid

-- If an absolute path is given,
-- it tries to remove the current working directory as prefix of it.
tryRemoveAbsolutePathComponent :: String -> IO String
tryRemoveAbsolutePathComponent f
    | "/" `isPrefixOf` f = do
                           dir <- getCurrentDirectory
                           return $ fromMaybe f (stripPrefix (dir ++ "/") f)
    | otherwise          = return f
