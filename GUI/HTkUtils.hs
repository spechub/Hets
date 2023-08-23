{-# LANGUAGE ExistentialQuantification #-}
{- |
Module      :  ./GUI/HTkUtils.hs
Copyright   :  (c) K. Luettich, Rene Wagner, Uni Bremen 2002-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (imports HTk)

Utilities on top of HTk
-}

module GUI.HTkUtils
  ( LBGoalView (..)
  , LBStatusIndicator (..)
  , EnableWid (..)
  , GUIMVar
  , listBox
  , errorMess
  , confirmMess
  , messageMess
  , askFileNameAndSave
  , createTextSaveDisplay
  , newFileDialogStr
  , fileDialogStr
  , displayTheoryWithWarning
  , populateGoalsListBox
  , indicatorFromProofStatus
  , indicatorFromBasicProof
  , indicatorString
  , enableWids
  , disableWids
  , enableWidsUponSelection
  , module X
  ) where

import System.Directory

import Util.Messages
import HTk.Toplevel.HTk as X hiding (x, y)
import HTk.Toolkit.ScrollBox as X
import HTk.Toolkit.SimpleForm as X
import HTk.Toolkit.TextDisplay as X
import HTk.Toolkit.FileDialog

import Logic.Prover
import Static.GTheory

import Common.DocUtils

import Control.Concurrent.MVar


-- ** some types

-- | Type for storing the proof management window
type GUIMVar = MVar (Maybe Toplevel)

-- | create a window with title and list of options, return selected option
listBox :: String -> [String] -> IO (Maybe Int)
listBox title entries =
  do
    main <- createToplevel [text title]
    lb <- newListBox main [value entries, bg "white", size (100, 39)] ::
             IO (ListBox String)
    pack lb [Side AtLeft, Expand On, Fill Both]
    scb <- newScrollBar main []
    pack scb [Side AtRight, Fill Y]
    lb # scrollbar Vertical scb
    (press, _) <- bindSimple lb (ButtonPress (Just 1))
    (closeWindow, _) <- bindSimple main Destroy
    sync ( (press >>> do
              sel <- getSelection lb
              destroy main
              return (case sel of
                 Just [i] -> Just i
                 _ -> Nothing) )
      +> (closeWindow >>> do
            destroy main
            return Nothing ))

{- |
Display some (longish) text in an uneditable, scrollable editor.
Returns immediately-- the display is forked off to separate thread. -}
createTextSaveDisplayExt :: String -- ^ title of the window
                         -> String -- ^ default filename for saving the text
                         -> String -- ^ text to be displayed
                         -> [Config Editor] {- ^ configuration options for
                         the text editor -}
                         -> IO () {- ^ action to be executed when
                         the window is closed -}
                         -> IO (Toplevel, Editor) {- ^ the window in which
                         the text is displayed -}
createTextSaveDisplayExt title fname txt conf upost =
  do win <- createToplevel [text title]
     b <- newFrame win [relief Groove, borderwidth (cm 0.05)]
     t <- newLabel b [text title, font (Helvetica, Roman, 18 :: Int)]
     q <- newButton b [text "Close", width 12]
     s <- newButton b [text "Save", width 12]
     (sb, ed) <- newScrollBox b (`newEditor` conf) []
     ed # state Disabled
     pack b [Side AtTop, Fill Both, Expand On]
     pack t [Side AtTop, Expand Off, PadY 10]
     pack sb [Side AtTop, Expand On, Fill Both]
     pack ed [Side AtTop, Expand On, Fill Both]
     pack q [Side AtRight, PadX 8, PadY 5]
     pack s [Side AtLeft, PadX 5, PadY 5]
     ed # state Normal
     ed # value txt
     ed # state Disabled
     forceFocus ed
     (editClicked, _) <- bindSimple ed (ButtonPress (Just 1))
     quit <- clicked q
     save <- clicked s
     _ <- spawnEvent $ forever $ quit >>> (destroy win >> upost)
       +> save >>> do
           disableButs q s
           askFileNameAndSave fname txt
           enableButs q s
           done
       +> editClicked >>> forceFocus ed
     return (win, ed)
   where disableButs b1 b2 = disable b1 >> disable b2
         enableButs b1 b2 = enable b1 >> enable b2
{- |
Display some (longish) text in an uneditable, scrollable editor.
Simplified version of createTextSaveDisplayExt -}
createTextSaveDisplay :: String -- ^ title of the window
                      -> String -- ^ default filename for saving the text
                      -> String -- ^ text to be displayed
                      -> IO ()
createTextSaveDisplay t f txt = do
  createTextSaveDisplayExt t f txt [size (100, 44)] done
  done

{- - added by KL

opens a FileDialog and saves to the selected file if OK is clicked
otherwise nothing happens -}
askFileNameAndSave :: String -- ^ default filename for saving the text
                   -> String -- ^ text to be saved
                   -> IO ()
askFileNameAndSave defFN txt =
    do curDir <- getCurrentDirectory
       selev <- newFileDialogStr "Save file" (curDir ++ '/' : defFN)
       mfile <- sync selev
       maybe done saveFile mfile
    where saveFile fp = writeFile fp txt

{- | returns a window displaying the given theory and the given
     warning text.
-}
displayTheoryWithWarning :: String -- ^ kind of theory
                         -> String -- ^ name of theory
                         -> String -- ^ warning text
                         -> G_theory -- ^ to be shown theory
                         -> IO ()
displayTheoryWithWarning kind thname warningTxt gth =
    let str = warningTxt ++ showDoc gth "\n"
        title = kind ++ " of " ++ thname
     in createTextSaveDisplay title (thname ++ ".dol") str

{- - added by RW
Represents the state of a goal in a 'ListBox' that uses 'populateGoalsListBox'
-}
data LBStatusIndicator = LBIndicatorProved
                       | LBIndicatorProvedInconsistent
                       | LBIndicatorDisproved
                       | LBIndicatorOpen
                       | LBIndicatorGuessed
                       | LBIndicatorConjectured
                       | LBIndicatorHandwritten

{- |
Converts a 'LBStatusIndicator' into a short 'String' representing it in
a 'ListBox' -}
indicatorString :: LBStatusIndicator
                -> String
indicatorString i = case i of
  LBIndicatorProved -> "[+]"
  LBIndicatorProvedInconsistent -> "[*]"
  LBIndicatorDisproved -> "[-]"
  LBIndicatorOpen -> "[ ]"
  LBIndicatorGuessed -> "[.]"
  LBIndicatorConjectured -> "[:]"
  LBIndicatorHandwritten -> "[/]"

{- |
Represents a goal in a 'ListBox' that uses 'populateGoalsListBox' -}
data LBGoalView = LBGoalView { -- | status indicator
                               statIndicator :: LBStatusIndicator,
                               -- | description
                               goalDescription :: String
                             }

{- |
Populates a 'ListBox' with goals. After the initial call to this function
the number of goals is assumed to remain constant in ensuing calls. -}
populateGoalsListBox :: ListBox String -- ^ listbox
                     -> [LBGoalView] {- ^ list of goals
length must remain constant after the first call -}
                     -> IO ()
populateGoalsListBox lb v = do
  selectedOld <- getSelection lb :: IO (Maybe [Int])
  lb # value (toString v)
  maybe (return ()) (mapM_ (`selection` lb)) selectedOld
  where
    toString = map (\ LBGoalView {statIndicator = i, goalDescription = d} ->
                        indicatorString i ++ ' ' : d)

-- | Converts a 'Logic.Prover.ProofStatus' into a 'LBStatusIndicator'
indicatorFromProofStatus :: ProofStatus a
                          -> LBStatusIndicator
indicatorFromProofStatus st = case goalStatus st of
  Proved c -> if c then LBIndicatorProved else LBIndicatorProvedInconsistent
  Disproved -> LBIndicatorDisproved
  Open _ -> LBIndicatorOpen

-- | Converts a 'BasicProof' into a 'LBStatusIndicator'
indicatorFromBasicProof :: BasicProof
                        -> LBStatusIndicator
indicatorFromBasicProof p = case p of
  BasicProof _ st -> indicatorFromProofStatus st
  Guessed -> LBIndicatorGuessed
  Conjectured -> LBIndicatorConjectured
  Handwritten -> LBIndicatorHandwritten

-- | existential type for widgets that can be enabled and disabled
data EnableWid = forall wid . HasEnable wid => EnW wid

enableWids :: [EnableWid] -> IO ()
enableWids = mapM_ $ \ ew -> case ew of
    EnW w -> enable w >> return ()

disableWids :: [EnableWid] -> IO ()
disableWids = mapM_ $ \ ew -> case ew of
    EnW w -> disable w >> return ()

{- | enables widgets only if at least one entry is selected in the listbox,
otherwise the widgets are disabled -}
enableWidsUponSelection :: ListBox String -> [EnableWid] -> IO ()
enableWidsUponSelection lb goalSpecificWids =
  (getSelection lb :: IO (Maybe [Int])) >>=
       maybe (disableWids goalSpecificWids)
             (const $ enableWids goalSpecificWids)
