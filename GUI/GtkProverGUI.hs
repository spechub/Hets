{- |
Module      :  $Header$
Description :  Gtk GUI for the prover
Copyright   :  (c) Thiemo Wiedemeyer, Uni Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  raider@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

This module provides a GUI for the prover.
-}

module GUI.GtkProverGUI ( showProverGUI ) where

import Graphics.UI.Gtk
import Graphics.UI.Gtk.Glade

import GUI.GtkUtils
import qualified GUI.Glade.ProverGUI as ProverGUI
import GUI.HTkProofDetails -- not implemented in Gtk

import Common.AS_Annotation as AS_Anno
import qualified Common.Doc as Pretty
import Common.Result
import qualified Common.OrderedMap as OMap
import Common.ExtSign

import Control.Monad ((<=<))
import Control.Concurrent.MVar

import Proofs.AbstractState

import Logic.Comorphism
import Logic.Logic
import Logic.Prover

import qualified Comorphisms.KnownProvers as KnownProvers

import Static.GTheory

import qualified Data.Map as Map
import Data.List
import Data.Maybe ( fromJust, fromMaybe, isJust )

data GProver = GProver { pName :: String
                       , prover :: G_prover
                       , comorphism :: [AnyComorphism]
                       , selected :: Int }

{- ProverGUI -}

-- | Displays the consistency checker window
showProverGUI :: Logic lid sublogics basic_spec sentence symb_items
                       symb_map_items sign morphism symbol raw_symbol proof_tree
  => lid
  -> ProofActions lid sentence -- ^ record of possible GUI actions
  -> String -- ^ theory name
  -> String -- ^ warning information
  -> G_theory -- ^ theory
  -> KnownProvers.KnownProversMap -- ^ map of known provers
  -> [(G_prover,AnyComorphism)] -- ^ list of suitable comorphisms to provers
                                -- for sublogic of G_theory
  -> IO (Result G_theory)
showProverGUI lid prGuiAcs thName warn th knownProvers comorphList = do
  initState <- (initialState lid thName th knownProvers comorphList
                >>= recalculateSublogicF prGuiAcs)
  state <- newMVar initState
  wait <- newEmptyMVar
  postGUIAsync $ do
    xml                   <- getGladeXML ProverGUI.get
    -- get objects
    window                <- xmlGetWidget xml castToWindow "ProverGUI"
    -- buttons at buttom
    btnShowTheory         <- xmlGetWidget xml castToButton "btnShowTheory"
    btnShowSelectedTheory <- xmlGetWidget xml castToButton "btnShowSelected"
    btnClose              <- xmlGetWidget xml castToButton "btnClose"
    -- goals view
    trvGoals              <- xmlGetWidget xml castToTreeView "trvGoals"
    btnGoalsAll           <- xmlGetWidget xml castToButton "btnGoalsAll"
    btnGoalsNone          <- xmlGetWidget xml castToButton "btnGoalsNone"
    btnGoalsInvert        <- xmlGetWidget xml castToButton "btnGoalsInvert"
    btnGoalsSelectOpen    <- xmlGetWidget xml castToButton "btnGoalsSelectOpen"
    -- axioms view
    trvAxioms             <- xmlGetWidget xml castToTreeView "trvAxioms"
    btnAxiomsAll          <- xmlGetWidget xml castToButton "btnAxiomsAll"
    btnAxiomsNone         <- xmlGetWidget xml castToButton "btnAxiomsNone"
    btnAxiomsInvert       <- xmlGetWidget xml castToButton "btnAxiomsInvert"
    btnAxiomsFormer       <- xmlGetWidget xml castToButton "btnAxiomsFormer"
    -- theorems view
    trvTheorems           <- xmlGetWidget xml castToTreeView "trvTheorems"
    btnTheoremsAll        <- xmlGetWidget xml castToButton "btnTheoremsAll"
    btnTheoremsNone       <- xmlGetWidget xml castToButton "btnTheoremsNone"
    btnTheoremsInvert     <- xmlGetWidget xml castToButton "btnTheoremsInvert"
    -- status
    btnDisplay            <- xmlGetWidget xml castToButton "btnDisplay"
    btnProofDetails       <- xmlGetWidget xml castToButton "btnProofDetails"
    btnProve              <- xmlGetWidget xml castToButton "btnProve"
    lblComorphism         <- xmlGetWidget xml castToLabel "lblComorphism"
    lblSublogic           <- xmlGetWidget xml castToLabel "lblSublogic"
    -- prover
    trvProvers            <- xmlGetWidget xml castToTreeView "trvProvers"
    btnFineGrained        <- xmlGetWidget xml castToButton "btnFineGrained"

    windowSetTitle window $ "Prove: " ++ thName

    axioms <- axiomMap initState

    -- set list data
    listProvers <- setListData trvProvers pName []
    listGoals <- setListData trvGoals show $ toGoals initState
    listAxioms <- setListData trvAxioms id $ toAxioms axioms
    listTheorems <- setListData trvTheorems id $ toTheorem initState

    let noProver = [ toWidget btnFineGrained
                   , toWidget btnProve
                   , toWidget lblComorphism
                   , toWidget lblSublogic ]
        noAxiom = [ toWidget btnAxiomsAll
                  , toWidget btnAxiomsNone
                  , toWidget btnAxiomsInvert
                  , toWidget btnAxiomsFormer ]
        noTheory = [ toWidget btnTheoremsAll
                   , toWidget btnTheoremsNone
                   , toWidget btnTheoremsInvert ]
        noGoal = [ toWidget btnGoalsAll
                 , toWidget btnGoalsNone
                 , toWidget btnGoalsInvert
                 , toWidget btnGoalsSelectOpen ]
        prove = noProver ++ noAxiom ++ noTheory ++ noGoal ++
                [ toWidget btnShowTheory
                , toWidget btnShowSelectedTheory
                , toWidget btnClose
                , toWidget btnProofDetails
                , toWidget btnDisplay ]
        update s' = do
          s <- updateGoals trvGoals listGoals =<<
               updateComorphism lblComorphism trvProvers listProvers =<<
               updateProver trvProvers listProvers =<<
               updateSublogic lblSublogic prGuiAcs knownProvers =<<
               setSelectedGoals trvGoals listGoals =<<
               setSelectedSens trvAxioms listAxioms trvTheorems listTheorems s'
          activate noProver
            (isJust (selectedProver s) && not (null $ selectedGoals s))
          return s

    activate noGoal (not $ OMap.null $ goalMap initState)
    activate noAxiom (not $ OMap.null axioms)
    activate noTheory (not $ OMap.null $ goalMap initState)

    -- setup provers list
    setListSelectorSingle trvProvers $ modifyMVar_ state $
      update <=< setSelectedProver trvProvers listProvers

    -- setup goal list
    setListSelectorMultiple trvGoals btnGoalsAll btnGoalsNone btnGoalsInvert $
      modifyMVar_ state update

    onClicked btnGoalsSelectOpen $ modifyMVar_ state $ \ s -> do
      sel <- treeViewGetSelection trvGoals
      treeSelectionSelectAll sel
      rs <- treeSelectionGetSelectedRows sel
      mapM_ ( \ p@(row:[]) -> do
        i <- listStoreGetValue listGoals row
        let isOpen st = let thst = thmStatus st in
              null thst || case maximum $ map snd thst of
                BasicProof _ pst -> isOpenGoal $ goalStatus pst
                _ -> False
        (if isOpen $ fromJust $ OMap.lookup (gName i) $ goalMap s
          then treeSelectionSelectPath else treeSelectionUnselectPath) sel p) rs
      update s

    -- setup axioms list
    setListSelectorMultiple trvAxioms btnAxiomsAll btnAxiomsNone btnAxiomsInvert
      $ modifyMVar_ state update

    onClicked btnAxiomsFormer $ modifyMVar_ state $ \ s -> do
      sel <- treeViewGetSelection trvAxioms
      treeSelectionSelectAll sel
      rs <- treeSelectionGetSelectedRows sel
      mapM_ ( \ p@(row:[]) -> do
        i <- listStoreGetValue listAxioms row
        (if wasTheorem $ fromJust $ OMap.lookup (stripPrefixAxiom i) axioms
          then treeSelectionUnselectPath else treeSelectionSelectPath) sel p) rs
      update s

    modifyMVar_ state $ update <=< updateProver trvProvers listProvers

    -- setup theorems list
    setListSelectorMultiple trvTheorems btnTheoremsAll btnTheoremsNone
                            btnTheoremsInvert $ modifyMVar_ state update

    -- button bindings
    onClicked btnClose $ widgetDestroy window

    onClicked btnShowTheory $ displayTheoryWithWarning "Theory" thName warn th

    onClicked btnShowSelectedTheory $ readMVar state >>=
      displayTheoryWithWarning "Selected Theory" thName warn . selectedTheory

    onClicked btnDisplay $ readMVar state >>= displayGoals

    onClicked btnProofDetails $ forkIO_ $ readMVar state >>= doShowProofDetails

    onClicked btnProve $ do
      activate prove False
      forkIOWithPostProcessing (readMVar state >>= proveF prGuiAcs)
        $ \ (Result ds ms) -> do
            s <- case ms of
              Nothing -> do
                errorDialog "Error" (showRelDiags 2 ds)
                takeMVar state
              Just res -> do
                takeMVar state
                return res
            activate prove True
            putMVar state =<< update s { proverRunning = False
                                       , accDiags = accDiags s ++ ds}

    onClicked btnFineGrained $ modifyMVar_ state $ \ s -> do
      mp <- fineGrainedSelection trvProvers listProvers
      update <=< updateProver trvProvers listProvers
        $ maybe s (\ p -> s { selectedProver = Just $ pName p }) mp

    onDestroy window $ putMVar wait ()

    widgetShow window

  _ <- takeMVar wait
  s <- takeMVar state
  case theory s of
    G_theory lidT sigT indT sensT _ -> do
      gMap <- coerceThSens (logicId s) lidT "ProverGUI last coerce" $ goalMap s
      return Result { diags = accDiags s
                    , maybeResult = Just $ G_theory lidT sigT indT
                                             (Map.union sensT gMap) startThId }

-- | Called whenever the button "Display" is clicked.
displayGoals :: Logic lid sublogics basic_spec sentence symb_items
                      symb_map_items sign morphism symbol raw_symbol proof_tree
             => ProofState lid sentence -> IO ()
displayGoals s = case theory s of
  G_theory lid1 (ExtSign sig1 _) _ _ _ -> do
    let thName = theoryName s
        goalsText = show . Pretty.vsep
          . map (print_named lid1 . AS_Anno.mapNamed (simplify_sen lid1 sig1))
          . toNamedList
        sens = selectedGoalMap s
    sens' <- coerceThSens (logicId s) lid1 "" sens
    textView ("Selected Goals from Theory " ++ thName) (goalsText sens')
             $ Just (thName ++ "-goals.txt")

fineGrainedSelection :: TreeView -> ListStore GProver -> IO (Maybe GProver)
fineGrainedSelection view list = do
  ps <- listStoreToList list
  selector <- treeViewGetSelection view
  if null ps then error "Cant make selection without sublogic!"
    else do
      ret <- listChoiceAux "Choose a translation"
               (\ (n,_,c) -> n ++ ": " ++ show c) $ concatMap expand ps
      case ret of
        Just (_,(n,_,c)) -> case findIndex ((n ==) . pName) ps of
          Just i -> let p = ps !! i in case findIndex (c ==) $ comorphism p of
            Just i' -> do
              let p' = p { selected = i' }
              listStoreSetValue list i p'
              treeSelectionSelectPath selector [i]
              return $ Just p'
            Nothing -> error "can't find selected comorphism"
          Nothing -> error "can't find selected prover"
        Nothing -> return Nothing

expand :: GProver -> [(String, G_prover, AnyComorphism)]
expand (GProver { pName = n, prover = p, comorphism = cs }) =
  map (\ c -> (n, p, c)) cs

updateSublogic :: Label -> ProofActions lid sentence
               -> KnownProvers.KnownProversMap -> ProofState lid sentence
               -> IO (ProofState lid sentence)
updateSublogic lbl prGuiAcs knownProvers s' = do
  s <- recalculateSublogicF prGuiAcs s' { proversMap = knownProvers }
  labelSetLabel lbl $ show $ sublogicOfTheory s
  return s

updateComorphism :: Label -> TreeView -> ListStore GProver
                 -> ProofState lid sentence -> IO (ProofState lid sentence)
updateComorphism lbl trvProvers listProvers s = do
  mprover <- getSelectedSingle trvProvers listProvers
  case mprover of
    Just (_, p) -> case comorphism p !! selected p of
      Comorphism cid -> let dN = drop 1 $ dropWhile (/= ';') $ language_name cid
        in labelSetLabel lbl $ if null dN then "identity" else dN
    Nothing -> return ()
  return s

updateProver :: TreeView -> ListStore GProver -> ProofState lid sentence
             -> IO (ProofState lid sentence)
updateProver trvProvers listProvers s = do
  let new = toProvers s
  old <- listStoreToList listProvers
  let prvs = map (\ p -> case find ((pName p ==) . pName) old of
          Nothing -> p
          Just p' -> let oldC = comorphism p' !! selected p' in
            p { selected = fromMaybe 0 $ findIndex (== oldC) $ comorphism p }
        ) new
      selFirst = do
        selectFirst trvProvers
        setSelectedProver trvProvers listProvers s
  updateListData listProvers prvs
  case selectedProver s of
    Just p -> case findIndex ((p ==) . pName) prvs of
      Just i -> do
        sel <- treeViewGetSelection trvProvers
        treeSelectionSelectPath sel [i]
        return s
      Nothing -> selFirst
    Nothing -> selFirst

updateGoals :: TreeView -> ListStore Goal -> ProofState lid sentence
            -> IO (ProofState lid sentence)
updateGoals trvGoals listGoals s = do
  updateListData listGoals $ toGoals s
  model <- treeViewGetModel trvGoals
  sel <- treeViewGetSelection trvGoals
  treeModelForeach (fromJust model) $ \ i -> do
    (row:[]) <- treeModelGetPath (fromJust model) i
    g <- listStoreGetValue listGoals row
    (if any (gName g ==) $ selectedGoals s
      then treeSelectionSelectIter else treeSelectionUnselectIter) sel i
    return False
  return s

setSelectedGoals :: TreeView -> ListStore Goal -> ProofState lid sentence
                 -> IO (ProofState lid sentence)
setSelectedGoals trvGoals listGoals s = do
  goals <- getSelectedMultiple trvGoals listGoals
  return s { selectedGoals = map (gName . snd) goals }

setSelectedSens :: TreeView -> ListStore String -> TreeView -> ListStore String
                -> ProofState lid sentence -> IO (ProofState lid sentence)
setSelectedSens axs listAxs ths listThs s = do
  axioms <- getSelectedMultiple axs listAxs
  theorems <- getSelectedMultiple ths listThs
  return s { includedAxioms   = map (stripPrefixAxiom . snd) axioms
           , includedTheorems = map snd theorems }

stripPrefixAxiom :: String -> String
stripPrefixAxiom a = case stripPrefix "(Th) " a of
  Just a' -> a'
  Nothing -> a

-- | Called whenever a prover is selected from the "Pick Theorem Prover" list.
setSelectedProver :: TreeView -> ListStore GProver -> ProofState lid sentence
                  -> IO (ProofState lid sentence)
setSelectedProver trvProvers listProvers s = do
  mprover <- getSelectedSingle trvProvers listProvers
  return s { selectedProver = maybe Nothing (Just . pName . snd) mprover }

toAxioms :: ThSens sentence (AnyComorphism, BasicProof) -> [String]
toAxioms =
  map (\ (k,s) -> if wasTheorem s then "(Th) " ++ k else k) . OMap.toList

toGoals :: ProofState lid sentence -> [Goal]
toGoals = map toGoal . OMap.toList . goalMap
  where toGoal (n, st) = let ts = thmStatus st in
          Goal { gName = n
               , gStatus = if null ts then GOpen
                           else basicProofToGStatus $ maximum $ map snd ts }

toTheorem :: ProofState lid sentence -> [String]
toTheorem = OMap.keys . goalMap

toProvers :: ProofState lid sentence -> [GProver]
toProvers = Map.elems . foldr (\ (p', c) m ->
    let n = getPName p'
        p = Map.findWithDefault (GProver n p' [] 0) n m in
    Map.insert n (p { comorphism = c : comorphism p}) m
  ) Map.empty . comorphismsToProvers
