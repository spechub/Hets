{- |
Module      :  $Header$
Description :  GUI for showing and saving proof details.
Copyright   :  (c) Rainer Grabbe 2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  needs POSIX

Additional window used by 'GUI.ProofManagement' for displaying proof details.
-}

module GUI.HTkProofDetails (doShowProofDetails) where

import qualified Common.Doc as Pretty
import qualified Common.OrderedMap as OMap

import qualified Data.Map as Map
import Data.Maybe
import Data.List
import Data.IORef
import Control.Monad (when)

import GUI.Utils (fileSaveDialog)

import System.Directory

import GUI.HTkUtils

import Proofs.AbstractState
import Logic.Comorphism
import Logic.Logic
import Logic.Prover
import Static.GTheory

-- * record structures and basic functions for handling

{- |
  Record structure containing proof details for a single proof.
-}
data GoalDescription = GoalDescription {
    proverInfo :: String, -- ^ standard proof details
    tacticScriptText :: OpenText, -- ^ more details for tactic script
    proofTreeText :: OpenText -- ^ more details for proof tree
    }

{- |
  Current state of a text tag providing additional information. The text can be
  folded or unfolded.
-}
data OpenText = OpenText {
    additionalText :: String, -- ^ additional information
    textShown :: Bool, -- ^ if true, text is unfolded (default: false)
    textStartPosition :: Position -- ^ start position in editor widget
    }

{- |
  Creates an initial 'GoalDescription' filled with just the standard prover
  info.
-}
emptyGoalDescription :: String -- ^ information about the used prover
                     -> GoalDescription -- ^ initiated GoalDescription
emptyGoalDescription st =
    GoalDescription {
      proverInfo = st,
      tacticScriptText = emptyOpenText,
      proofTreeText = emptyOpenText }

{- |
  Creates an empty 'OpenText' with start position (0,0).
-}
emptyOpenText :: OpenText
emptyOpenText = OpenText {
      additionalText = "",
      textShown = False,
      textStartPosition = (Distance 0, Distance 0) }

-- | Determines the kind of content of a 'HTk.TextTag'.
data Content = TacticScriptText | ProofTreeText deriving Eq


-- * GUI for show proof details

-- ** help functions

{- | Return number of new lines in a string.
-}
numberOfLines :: String
              -> Int
numberOfLines =
    foldr (\ ch -> if ch == '\n' then (+ 1) else id) 0

{- |
  Change the x-value of a 'Position' by a given arithmetical function and value.
-}
changePosition :: (Int -> Int -> Int)  -- ^ mostly add or subtract values
               -> Int -- ^ (difference) value
               -> Position -- ^ old position
               -> Position -- ^ changed position with new x-value
changePosition f diff (Distance posX, Distance posY) =
    (Distance $ f posX diff, Distance posY)

{- |
  Indentation of a 'String' (also multiple lines) by a number of spaces.
-}
indent :: Int -- ^ number of spaces
       -> String -- ^ input String
       -> Pretty.Doc -- ^ output document
indent numSp st =
  Pretty.text (replicate numSp ' ') Pretty.<>
    (Pretty.vcat . map Pretty.text . lines) st

{- |
  Standard indent width.
-}
stdIndent :: Int
stdIndent = 4

{- |
  An item of thmStatus will be put into 'GoalDescription' structure.
  Pretty printing of proof details, adding additional information
  for text tags.
-}
fillGoalDescription :: (AnyComorphism, BasicProof)
                    -> GoalDescription -- ^ contents in pretty format
fillGoalDescription (cmo, basicProof) =
    let gd = indent stdIndent $ show $ printCmWStat (cmo, basicProof)
        stat str = Pretty.text "Status:" Pretty.<+> Pretty.text str
        printCmWStat (c, bp) =
            Pretty.text "Com:" Pretty.<+> Pretty.text (show c)
            Pretty.$+$ indent stdIndent (show $ printBP bp)
        printBP bp = case bp of
                     BasicProof _ ps ->
                      stat (show $ goalStatus ps) Pretty.$+$
                      (case goalStatus ps of
                       Proved _ -> Pretty.text "Used axioms:" Pretty.<+>
                           Pretty.fsep (Pretty.punctuate Pretty.comma
                             $ map (Pretty.text . show) $ usedAxioms ps)
                           Pretty.$+$ Pretty.text "Used time:" Pretty.<+>
                                 Pretty.text (show $ usedTime ps)
                       _ -> Pretty.empty)
                      Pretty.$+$ Pretty.text "Prover:" Pretty.<+>
                            Pretty.text (usedProver ps)
                     otherProof -> stat (show otherProof)
        printTS bp = case bp of
                     BasicProof _ ps ->
                       indent (2 * stdIndent) $ (\(TacticScript xs) -> xs) $
                                                tacticScript ps
                     _ -> Pretty.empty
        printPT bp = case bp of
                     BasicProof _ ps ->
                       indent (2 * stdIndent) $ show $ proofTree ps
                     _ -> Pretty.empty
    in  (emptyGoalDescription $ show gd) {
           tacticScriptText = emptyOpenText {
             additionalText = show $ printTS basicProof },
           proofTreeText = emptyOpenText {
             additionalText = show $ printPT basicProof } }

{- |
  Gets real 'EndOfText' index at the char position after (in x-direction)
  the last written text. This is because 'EndOfText' only gives a value where a
  text would be after an imaginary newline.
-}
getRealEndOfTextIndex :: Editor -- ^ the editor whose end index is determined
                      -> IO Position -- ^ position behind last char in widget
getRealEndOfTextIndex ed = do
    (Distance eotX, _) <- getIndexPosition ed EndOfText
    lineBefore <- getTextLine ed $ IndexPos (Distance (eotX - 1), 0)
    return (Distance eotX - 1, Distance $ length lineBefore)

{- |
  For a given Ordered Map containing all proof values, this function adapts the
  text positions lying behind after a given reference position. This is called
  when a position in the text is moved after clicking a text tag button.
-}
adaptTextPositions :: (Int -> Int -> Int)  -- ^ mostly add or subtract values
                   -> Int -- ^ (difference) value
                   -> Position -- ^ reference Position
                   -> OMap.OMap (String, Int) GoalDescription
                      -- ^ Map for all proofs
                   -> OMap.OMap (String, Int) GoalDescription -- ^ adapted Map
adaptTextPositions f diff pos =
    OMap.map $ \ gDesc ->
      let tst = tacticScriptText gDesc
          ptt = proofTreeText gDesc
      in gDesc {
           tacticScriptText = if textStartPosition tst > pos
               then tst { textStartPosition = changePosition f diff $
                                textStartPosition tst }
               else tst,
           proofTreeText = if textStartPosition ptt > pos
               then ptt { textStartPosition = changePosition f diff $
                                textStartPosition ptt }
               else ptt }

-- ** main GUI

{- |
  Called whenever the button /Show proof details/ is clicked.
-}
doShowProofDetails ::
    (Logic lid
           sublogics1
           basic_spec1
           sentence
           symb_items1
           symb_map_items1
           sign1
           morphism1
           symbol1
           raw_symbol1
           proof_tree1) =>
       ProofState lid sentence
    -> IO ()
doShowProofDetails prGUISt =
   do
    let thName = theoryName prGUISt
        winTitleStr = "Proof Details of Selected Goals from Theory " ++ thName
    win       <- createToplevel [text winTitleStr]
    bFrame    <- newFrame win [relief Groove, borderwidth (cm 0.05)]
    winTitle  <- newLabel bFrame [text winTitleStr,
                                  font (Helvetica, Roman, 18::Int)]
    btnBox    <- newHBox bFrame []
    tsBut     <- newButton btnBox [text expand_tacticScripts, width 18]
    ptBut     <- newButton btnBox [text expand_proofTrees, width 18]
    sBut      <- newButton btnBox [text "Save", width 12]
    qBut      <- newButton btnBox [text "Close", width 12]
    pack winTitle [Side AtTop, Expand Off, PadY 10]

    (sb, ed) <- newScrollBox bFrame
        (flip newEditor [state Normal, size(80,40)]) []
    ed # state Disabled
    pack bFrame [Side AtTop, Expand On, Fill Both]
    pack sb     [Side AtTop, Expand On, Fill Both]
    pack ed     [Side AtTop, Expand On, Fill Both]

    pack btnBox [Side AtTop, Expand On, Fill X]
    pack tsBut [PadX 5, PadY 5]
    pack ptBut [PadX 5, PadY 5]
    pack sBut  [PadX 5, PadY 5]
    pack qBut  [PadX 8, PadY 5]

    let sttDesc = "Tactic script"
        sptDesc = "Proof tree"
        sens = selectedGoalMap prGUISt
        elementMap = foldr insertSenSt Map.empty (reverse $ OMap.toList sens)
        insertSenSt (gN, st) resOMap =
            foldl (flip $ \ (s2, ind) -> OMap.insert (gN, ind) $
                                                     fillGoalDescription s2)
              resOMap $
               zip (sortBy (\ (_,a) (_,b) -> compare a b) $ thmStatus st)
                   [(0::Int)..]

    stateRef <- newIORef elementMap
    ed # state Normal
    mapM_ (\ ((gName, ind), goalDesc) -> do
        when (ind == 0) $
          appendText ed $ replicate 75 '-' ++ "\n" ++ gName ++ "\n"
        appendText ed $ proverInfo goalDesc ++ "\n"
        opTextTS <- addTextTagButton sttDesc (tacticScriptText goalDesc)
                       TacticScriptText ed (gName, ind) stateRef
        opTextPT <- addTextTagButton sptDesc (proofTreeText goalDesc)
                       ProofTreeText ed (gName, ind) stateRef
        appendText ed "\n"
        let goalDesc' = goalDesc{ tacticScriptText = opTextTS,
                                  proofTreeText    = opTextPT }
        modifyIORef stateRef (OMap.update (\ _ -> Just goalDesc') (gName, ind))
      ) $ OMap.toList elementMap

    ed # state Disabled

    (editClicked, _) <- bindSimple ed (ButtonPress (Just 1))
    quit <- clicked qBut
    save <- clicked sBut
    toggleTacticScript <- clicked tsBut
    toggleProofTree <- clicked ptBut
    btnState <- newIORef (False, False)
    _ <- spawnEvent $ forever
        $ quit >>> destroy win
        +> save >>> do
          disable qBut
          disable sBut
          curDir <- getCurrentDirectory
          let f = curDir ++ '/' : thName ++ "-proof-details.txt"
          mfile <- fileSaveDialog f [ ("Text",["*.txt"])
                                    , ("All Files",["*"])] Nothing
          maybe done (writeTextToFile ed) mfile
          enable qBut
          enable sBut
          done
        +> toggleTacticScript >>> do
             (expTS, expPT) <- readIORef btnState
             tsBut # text (if expTS then expand_tacticScripts
                                    else hide_tacticScripts)
             toggleMultipleTags TacticScriptText expTS ed stateRef
             writeIORef btnState (not expTS, expPT)
        +> toggleProofTree >>> do
             (expTS, expPT) <- readIORef btnState
             ptBut # text (if expPT then expand_proofTrees
                                    else hide_proofTrees)
             toggleMultipleTags ProofTreeText expPT ed stateRef
             writeIORef btnState (expTS, not expPT)
        +> editClicked >>> forceFocus ed
    return ()
  where
    expand_tacticScripts = "Expand tactic scripts"
    expand_proofTrees = "Expand proof trees"
    hide_tacticScripts = "Hide tactic scripts"
    hide_proofTrees = "Hide proof trees"

{- |
  Toggle all 'TextTag's of one kind to the same state (visible or invisible),
  either tactic script or proof tree.
-}
toggleMultipleTags :: Content -- ^ kind of text tag to toggle
                   -> Bool -- ^ current visibility state
                   -> Editor
                      -- ^ editor window to which button will be attached
                   -> IORef (OMap.OMap (String, Int) GoalDescription)
                      -- ^ current state of all proof descriptions
                   -> IO ()
toggleMultipleTags content expanded ed stateRef = do
    s <- readIORef stateRef
    mapM_ (\ (dKey, goalDesc) -> do
        let openText = if content == TacticScriptText
                         then tacticScriptText goalDesc
                         else proofTreeText goalDesc
        when (textShown openText == expanded)
             (toggleTextTag content ed dKey stateRef)
      ) $ OMap.toList s
    done

{- |
  This functions toggles the state from a given TextTag from visible to
  invisible or vice versa. This depends on the current state in the ordered map
  of goal descriptions. First parameter indicates whether the tactic script
  or the proof tree text from a goal description will be toggled.
-}
toggleTextTag :: Content -- ^ kind of text tag to toggle
              -> Editor -- ^ editor window to which button will be attached
              -> (String, Int) -- ^ key in single proof descriptions
                               -- (goal name and index)
              -> IORef (OMap.OMap (String, Int) GoalDescription)
                 -- ^ current state of all proof descriptions
              -> IO ()
toggleTextTag content ed (gName, ind) stateRef = do
    s <- readIORef stateRef
    let gd = fromMaybe (emptyGoalDescription gName)
             $ OMap.lookup (gName, ind) s
        openText = if content == TacticScriptText then tacticScriptText gd
                                                    else proofTreeText gd
        tsp = textStartPosition openText
        nol = (numberOfLines $ additionalText openText)
    if not $ textShown openText then do
        ed # state Normal
        insertText ed tsp $ additionalText openText
        ed # state Disabled
        done
      else do
        ed # state Normal
        deleteTextRange ed tsp $ changePosition (+) nol tsp
        ed # state Disabled
        done
    let openText' = openText { textShown = not $ textShown openText }
        s' = OMap.update
                 (\_ -> Just $ if content == TacticScriptText
                          then gd{ tacticScriptText = openText' }
                          else gd{ proofTreeText =  openText' } )
                 (gName, ind) s
    writeIORef stateRef $ adaptTextPositions
         (if textShown openText then (-) else (+))
         nol tsp s'

{- |
  A button in form of a text tag will be added to the specified editor window.
  The events for clicking on a button are set up: adding or removing
  additional text lines by alternately clicking. All positions of text lying
  behind have to be adapted.
  The current state of text tags is stored and modified in 'IORef'.
  Initial call of this function returns an 'OpenText' containing the status of
  the added text tag button.
-}
addTextTagButton :: String -- ^ caption for button
                 -> OpenText -- ^ conatins text to be outfolded if clicked
                 -> Content -- ^ either text from tacticScript or proofTree
                 -> Editor -- ^ editor window to which button will be attached
                 -> (String, Int) -- ^ key in single proof descriptions
                                  -- (goal name and index)
                 -> IORef (OMap.OMap (String, Int) GoalDescription)
                    -- ^ current state of all proof descriptions
                 -> IO OpenText -- ^ information about OpenText status
addTextTagButton cap addText content ed dKey stateRef = do
    appendText ed $ replicate (2 * stdIndent) ' '
    curPosStart <- getRealEndOfTextIndex ed
    appendText ed cap
    curPosEnd <- getRealEndOfTextIndex ed
    insertNewline ed
    ttag <- createTextTag ed curPosStart curPosEnd [underlined On]

    (selectTextTag, _) <- bindSimple ttag (ButtonPress (Just 1))
    (enterTT, _) <- bindSimple ttag Enter
    (leaveTT, _) <- bindSimple ttag Leave
    _ <- spawnEvent $ forever
                   $ selectTextTag >>> toggleTextTag content ed dKey stateRef
                   +> enterTT >>> do
                     ed # cursor hand2
                     done
                   +> leaveTT >>> do
                     ed # cursor xterm
                     done
    return OpenText {additionalText = "\n" ++ additionalText addText ++ "\n",
                     textShown = False,
                     textStartPosition = curPosEnd}
