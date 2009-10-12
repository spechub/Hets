{- |
Module      :  $Header$
Description :  Access to the .glade files stored as strings inside the binary
Copyright   :  (c) Thiemo Wiedemeyer, Uni Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  raider@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable

This module provides the ability to store xml stings in a temporary file to load
it with gtk2hs. This is needed, because gtk2hs needs glade files for input, but
we want to distribute them within the binary.
-}

module GUI.GtkUtils
  ( getGladeXML
  , startMainLoop
  , stopMainLoop
  , forkIO_
  , forkIOWithPostProcessing

  -- * Windows for use inside Gtk thread
  , infoDialog
  , errorDialog
  , warningDialog
  , questionDialog

  , fileOpenDialog
  , fileSaveDialog

  , listChoiceAux
  , listChoice

  , progressBar
  , pulseBar

  , textView
  , displayTheory
  , displayTheoryWithWarning

  -- * Windows for use in Gtk windows
  , infoDialogExt
  , errorDialogExt
  , warningDialogExt
  , questionDialogExt

  , fileOpenDialogExt
  , fileSaveDialogExt

  , listChoiceExt

  , progressBarExt
  , pulseBarExt

  , textViewExt
  , displayTheoryExt
  , displayTheoryWithWarningExt

  -- * Frequently used functions inside Gtk thread
  , setListData
  , updateListData
  , setListSelectorSingle
  , setListSelectorMultiple
  , selectFirst
  , getSelectedSingle
  , getSelectedMultiple

  , selectAll
  , selectNone
  , selectInvert
  )
  where

import Graphics.UI.Gtk
import Graphics.UI.Gtk.Glade

import qualified GUI.Glade.Utils as Utils

import Static.GTheory (G_theory)
import Common.DocUtils (showDoc)

import Control.Concurrent (forkIO)
import Control.Monad (when)

import System.Directory ( removeFile, getTemporaryDirectory, doesFileExist
                        , canonicalizePath)
import System.FilePath (takeFileName, takeDirectory)
import System.IO (hFlush, hClose, hPutStr, openTempFile)

import Data.IORef

-- | Returns a GladeXML Object of a xmlstring.
getGladeXML :: (String, String) -> IO GladeXML
getGladeXML (name, xmlstr) = do
  temp <- getTemporaryDirectory
  (filename, handle) <- openTempFile temp name
  hPutStr handle xmlstr
  hFlush handle
  mxml <- xmlNew filename
  hClose handle
  removeFile filename
  case mxml of
    Just xml -> return xml
    Nothing -> error "GtkUtils: Can't load xml string."

-- | Starts the gtk main event loop in a thread
startMainLoop :: IO ()
startMainLoop = forkIO_ $ do
  unsafeInitGUIForThreadedRTS
  mainGUI

stopMainLoop :: IO ()
stopMainLoop = postGUISync mainQuit

forkIO_ :: IO () -> IO ()
forkIO_ f = do
  forkIO f
  return ()

forkIOWithPostProcessing :: IO a -> (a -> IO ()) -> IO ()
forkIOWithPostProcessing action post = forkIO_ $ do
  result <- action
  postGUIAsync $ post result

{- * Usefull windows and function.
     !!! IMPORTANT for all following functions !!!
     Functions for use outside of the Gtk thread have a "Ext" postfix.
     All other functions must be called from inside the Gtk thread. -}

-- | Dialog for different typed messages
dialog :: MessageType -- ^ Dialogtype
       -> String -- ^ Title
       -> String -- ^ Message
       -> Maybe (IO()) -- ^ Action on Ok, Yes
       -> IO Bool
dialog messageType title message mAction = do
  dlg <- case messageType of
    MessageInfo ->
      messageDialogNew Nothing [] messageType ButtonsOk message
    MessageWarning ->
      messageDialogNew Nothing [] messageType ButtonsYesNo message
    MessageQuestion ->
      messageDialogNew Nothing [] messageType ButtonsYesNo message
    _ ->
      messageDialogNew Nothing [] messageType ButtonsOk message

  windowSetTitle dlg title

  response <- dialogRun dlg
  choice <- case response of
    ResponseOk -> return True
    ResponseYes -> return True
    _ -> return False

  widgetDestroy dlg
  if choice then
    case mAction of
      Just action -> do
        forkIO action
        return choice
      Nothing -> return choice
    else return choice

-- | create a window which displays a given text
infoDialog :: String -- ^ Title
           -> String -- ^ Message
           -> IO ()
infoDialog title message = do
  dialog MessageInfo title message Nothing
  return ()

-- | create a window which displays a given text
infoDialogExt :: String -- ^ Title
              -> String -- ^ Message
              -> IO ()
infoDialogExt title = postGUISync . infoDialog title

-- | create a window which displays a given error
errorDialog :: String -- ^ Title
            -> String -- ^ Message
            -> IO ()
errorDialog title message = do
  dialog MessageError title message Nothing
  return ()

-- | create a window which displays a given error
errorDialogExt :: String -- ^ Title
               -> String -- ^ Message
               -> IO ()
errorDialogExt title = postGUISync . errorDialog title

-- | create a window which displays a given warning and ask for continue
warningDialog :: String -- ^ Title
              -> String -- ^ Message
              -> Maybe (IO ()) -- ^ Action on Ok
              -> IO Bool
warningDialog = dialog MessageWarning

-- | create a window which displays a given warning and ask for continue
warningDialogExt :: String -- ^ Title
                 -> String -- ^ Message
                 -> Maybe (IO ()) -- ^ Action on Ok
                 -> IO Bool
warningDialogExt title message  = postGUISync . warningDialog title message

-- | create a window which displays a given question
questionDialog :: String  -- ^ Title
               -> String  -- ^ Message
               -> Maybe (IO ()) -- ^ Action on Yes
               -> IO Bool
questionDialog = dialog MessageQuestion

-- | create a window which displays a given question
questionDialogExt :: String  -- ^ Title
                  -> String  -- ^ Message
                  -> Maybe (IO ()) -- ^ Action on Yes
                  -> IO Bool
questionDialogExt title message = postGUISync . questionDialog title message


-- | Filedialog for opening and saving
fileDialog :: FileChooserAction -- ^ Action
           -> FilePath -- ^ Defaultname for file
           -> [(String, [String])] -- ^ Filter (name, pattern list)
           -> Maybe (FilePath -> IO ()) -- ^ Action on open
           -> IO (Maybe FilePath)
fileDialog fAction fname' filters mAction = do
  fname <- canonicalizePath fname'
  dlg <- case fAction of
    FileChooserActionOpen -> do
      dlg' <-fileChooserDialogNew Nothing Nothing FileChooserActionOpen
                                  [ (stockCancel, ResponseCancel)
                                  , (stockOpen,   ResponseAccept)]
      fileChooserSetCurrentFolder dlg' $ takeDirectory fname
      fileChooserSetFilename dlg' $ takeFileName fname
      return dlg'
    FileChooserActionSave -> do
      dlg' <- fileChooserDialogNew Nothing Nothing FileChooserActionSave
                                   [ (stockCancel, ResponseCancel)
                                   , (stockSave,   ResponseAccept)]
      fileChooserSetCurrentFolder dlg' $ takeDirectory fname
      fileChooserSetCurrentName dlg' $ takeFileName fname
      return dlg'
    _ -> error "FileDialog: Wrong Type"

  mapM_ (\ (name, pattern) -> do
          fileFilter <- fileFilterNew
          mapM_ (fileFilterAddPattern fileFilter) pattern
          fileFilterSetName fileFilter name
          fileChooserAddFilter dlg fileFilter
        ) filters

  response <- dialogRun dlg
  ret <- case response of
    ResponseCancel -> return Nothing
    ResponseAccept -> do
      mpath <- fileChooserGetFilename dlg
      case mpath of
        Just path -> do
          exist <- doesFileExist path
          answer <- if exist then
            dialog MessageQuestion "File already exist"
                   "Are you sure to overwrite existing file?" Nothing
            else return True
          if answer then
            case mAction of
              Just action -> do
                action path
                return mpath
              Nothing -> return mpath
            else return Nothing
        Nothing -> return Nothing
    _ -> return Nothing
  widgetDestroy dlg
  return ret

fileOpenDialog :: FilePath -- ^ Defaultname for file
               -> [(String, [String])] -- ^ Filter (name, pattern list)
               -> Maybe (FilePath -> IO ()) -- ^ Action on open
               -> IO (Maybe FilePath)
fileOpenDialog = fileDialog FileChooserActionOpen

fileOpenDialogExt :: FilePath -- ^ Defaultname for file
                  -> [(String, [String])] -- ^ Filter (name, pattern list)
                  -> Maybe (FilePath -> IO ()) -- ^ Action on open
                  -> IO (Maybe FilePath)
fileOpenDialogExt p f = postGUISync . fileOpenDialog p f

fileSaveDialog :: FilePath -- ^ Defaultname for file
               -> [(String, [String])] -- ^ Filter (name, pattern list)
               -> Maybe (FilePath -> IO ()) -- ^ Action on save
               -> IO (Maybe FilePath)
fileSaveDialog = fileDialog FileChooserActionSave

fileSaveDialogExt :: FilePath -- ^ Defaultname for file
                  -> [(String, [String])] -- ^ Filter (name, pattern list)
                  -> Maybe (FilePath -> IO ()) -- ^ Action on save
                  -> IO (Maybe FilePath)
fileSaveDialogExt p f = postGUISync . fileSaveDialog p f

-- | create a window with title and list of options, return selected option
listChoiceAux :: String -- ^ Title
              -> (a -> String) -- ^ Name of element
              -> [a] -- ^ Rows to display
              -> IO (Maybe (Int,a)) -- ^ Selected row
listChoiceAux title showF items  = do
  xml     <- getGladeXML Utils.get
  -- get objects
  dlg     <- xmlGetWidget xml castToDialog "ListView"
  trvList <- xmlGetWidget xml castToTreeView "trvList"

  windowSetTitle dlg title
  store <- setListData trvList showF items
  selector <- treeViewGetSelection trvList
  setListSelectorSingle trvList (return ())
  mIter <- treeModelGetIterFirst store
  case mIter of
    Just iter -> treeSelectionSelectIter selector iter
    Nothing -> return ()

  dialogAddButton dlg stockCancel ResponseCancel
  dialogAddButton dlg stockOk ResponseOk

  response <- dialogRun dlg
  ret <- case response of
    ResponseCancel -> return Nothing
    ResponseOk -> getSelectedSingle trvList store
    _ -> return Nothing
  widgetDestroy dlg
  return ret

-- | create a window with title and list of options, return selected option
listChoice :: String -- ^ Title
           -> [String] -- ^ Rows to display
           -> IO (Maybe Int) -- ^ Selected row
listChoice title items = do
  ret <- listChoiceAux title id items
  return $ maybe Nothing (\ (i,_) -> Just i) ret

-- | create a window with title and list of options, return selected option
listChoiceExt :: String -- ^ Title
              -> [String] -- ^ Rows to display
              -> IO (Maybe Int) -- ^ Selected row
listChoiceExt title = postGUISync . listChoice title

-- | Progress/Pulse bar window
progressBarAux :: Bool -- ^ Percent or pulse
               -> String -- ^ Title
               -> String -- ^ Description
               -> IO (Double -> String -> IO (), IO ())
progressBarAux isProgress title description = do
  xml         <- getGladeXML Utils.get
  -- get window
  window      <- xmlGetWidget xml castToWindow "ProgressBar"
  -- get progress bar
  bar <- xmlGetWidget xml castToProgressBar "pbProgress"

  windowSetTitle window title
  progressBarSetText bar description
  progressBarSetPulseStep bar 0.05
  windowSetPosition window WinPosCenter
  windowSetTypeHint window WindowTypeHintUtility

  exit <- if isProgress then return (widgetDestroy window) else do
    h <- timeoutAdd (do
                      progressBarPulse bar
                      return True
                    ) 75
    return (do timeoutRemove h; widgetDestroy window)

  widgetShow window

  let update p d = do
        progressBarSetText bar d
        when isProgress $ progressBarSetFraction bar p

  return (update, exit)


progressBar :: String -- ^ Title
            -> String -- ^ Description
            -> IO (Double -> String -> IO (), IO ())
progressBar = progressBarAux True

progressBarExt :: String -- ^ Title
               -> String -- ^ Description
               -> IO (Double -> String -> IO (), IO ())
progressBarExt title description = do
  (update, exit) <- postGUISync $ progressBar title description
  return (\ a -> postGUISync . update a, postGUISync exit)

pulseBar :: String -- ^ Title
         -> String -- ^ Description
         -> IO (String -> IO (), IO ())
pulseBar title description = do
  (update, exit) <- progressBarAux False title description
  let update' = update 0
  return (update', exit)

pulseBarExt :: String -- ^ Title
            -> String -- ^ Description
            -> IO (String -> IO (), IO ())
pulseBarExt title description = do
  (update, exit) <- postGUISync $ pulseBar title description
  return (postGUISync . update, postGUISync exit)

-- | Display text in an uneditable, scrollable editor. Not blocking!
textView :: String -- ^ Title
         -> String -- ^ Message
         -> Maybe (FilePath) -- ^ Filename
         -> IO ()
textView title message mfile = do
  xml     <- getGladeXML Utils.get
  -- get objects
  dlg    <- xmlGetWidget xml castToDialog "TextView"
  tvText <- xmlGetWidget xml castToTextView "tvText"

  windowSetTitle dlg title
  buffer <- textViewGetBuffer tvText
  textBufferInsertAtCursor buffer message

  tagTable <- textBufferGetTagTable buffer
  font <- textTagNew Nothing
  set font [ textTagFont := "FreeMono" ]
  textTagTableAdd tagTable font
  start <- textBufferGetStartIter buffer
  end <- textBufferGetEndIter buffer
  textBufferApplyTag buffer font start end

  case mfile of
    Just file -> do
      btnSave <- dialogAddButton dlg stockSave ResponseNone
      onClicked btnSave $ do
        fileDialog FileChooserActionSave file
                   [("Nothing", ["*"]), ("Text", ["*.txt"])]
                   $ Just (\ filepath -> writeFile filepath message)
        return ()
      return ()
    Nothing -> return ()

  btnClose <- dialogAddButton dlg stockClose ResponseNone
  onClicked btnClose $ widgetDestroy dlg

  widgetShow dlg
  return ()

-- | Display text in an uneditable, scrollable editor. Not blocking!
textViewExt :: String -- ^ Title
         -> String -- ^ Message
         -> Maybe (FilePath) -- ^ Filename
         -> IO ()
textViewExt title message = postGUIAsync . textView title message

-- | displays a theory in a window
displayTheory :: String -- ^ Kind of theory
              -> String -- ^ Name of theory
              -> G_theory -- ^ Theory
              -> IO ()
displayTheory kind name gth =
  textView ( kind ++ " of " ++ name) (showDoc gth "\n") $ Just $ name ++ ".het"

-- | displays a theory in a window
displayTheoryExt :: String -- ^ Kind of theory
                 -> String -- ^ Name of theory
                 -> G_theory -- ^ Theory
                 -> IO ()
displayTheoryExt kind name = postGUIAsync . displayTheory kind name

-- | displays a theory with warning in a window
displayTheoryWithWarning :: String -- ^ Kind of theory
                         -> String -- ^ Name of theory
                         -> String -- ^ Warning
                         -> G_theory -- ^ Theory
                         -> IO ()
displayTheoryWithWarning k n w t =
  textView (k ++ " of " ++ n) (w ++ showDoc t "\n") $ Just $ n ++ ".het"

-- | displays a theory with warning in a window
displayTheoryWithWarningExt :: String -- ^ Kind of theory
                            -> String -- ^ Name of theory
                            -> String -- ^ Warning
                            -> G_theory -- ^ Theory
                            -> IO ()
displayTheoryWithWarningExt k n w =
  postGUIAsync . displayTheoryWithWarning k n w

-- * Frequently used functions

-- | Setup list with single selection
setListSelectorSingle :: TreeView -> IO () -> IO ()
setListSelectorSingle view action= do
  selector <- treeViewGetSelection view
  treeSelectionSetMode selector SelectionSingle
  onCursorChanged view action
  selectFirst view
  return ()

-- | Setup list with multiple selection
setListSelectorMultiple :: TreeView -> Button -> Button -> Button -> IO ()
                        -> IO (IORef [TreePath])
setListSelectorMultiple view btnAll btnNone btnInvert action = do
  selector <- treeViewGetSelection view
  treeSelectionSetMode selector SelectionMultiple
  ioRefSelection <- newIORef ([] :: [TreePath])

  -- setup selector
  onCursorChanged view $ do
    s' <- treeSelectionGetSelectedRows selector
    s <- readIORef ioRefSelection
    let newSelection = [ x | x <- s', notElem x s]
                    ++ [ x | x <- s, notElem x s']
    writeIORef ioRefSelection newSelection
    treeSelectionUnselectAll selector
    mapM_ (treeSelectionSelectPath selector) newSelection
    action

  treeSelectionSelectAll selector

  -- setup buttons
  onClicked btnAll $ do selectAll view ioRefSelection; action
  onClicked btnNone $ do selectNone view ioRefSelection; action
  onClicked btnInvert $ do selectInvert view ioRefSelection; action

  return ioRefSelection

-- | Selects the first item if possible
selectFirst :: TreeView -> IO ()
selectFirst view = do
  mModel <- treeViewGetModel view
  case mModel of
    Nothing -> return ()
    Just model -> do
      mIter <- treeModelGetIterFirst model
      case mIter of
        Nothing -> return ()
        Just iter -> do
          selector <- treeViewGetSelection view
          treeSelectionSelectIter selector iter
          path <- treeModelGetPath model iter
          treeViewSetCursor view path Nothing

-- | Get selected item
getSelectedSingle :: TreeView -> ListStore a -> IO (Maybe (Int,a))
getSelectedSingle view list = do
  mModel <- treeViewGetModel view
  case mModel of
    Nothing -> return Nothing
    Just model -> do
      selector <- treeViewGetSelection view
      mIter <- treeSelectionGetSelected selector
      case mIter of
        Nothing -> return Nothing
        Just iter -> do
          path <- treeModelGetPath model iter
          case path of
            row:[] -> do
              item <- listStoreGetValue list row
              return $ Just (row, item)
            _ -> error "List type not supported"

-- | Get selected items and row number
getSelectedMultiple :: TreeView -> ListStore a -> IO [(Int,a)]
getSelectedMultiple view list = do
  selector <- treeViewGetSelection view
  rows' <- treeSelectionGetSelectedRows selector
  let rows = map head rows'
  items <- mapM (listStoreGetValue list) rows
  return $ zip rows items

-- | Select all rows
selectAll :: TreeView -> IORef [TreePath] -> IO ()
selectAll view ioRefSelection = do
  selector <- treeViewGetSelection view
  treeSelectionSelectAll selector
  s <- treeSelectionGetSelectedRows selector
  writeIORef ioRefSelection s

-- | Deselect all rows
selectNone :: TreeView -> IORef [TreePath] -> IO ()
selectNone view ioRefSelection = do
  selector <- treeViewGetSelection view
  treeSelectionUnselectAll selector
  writeIORef ioRefSelection []

-- | Invert selection of list
selectInvert :: TreeView -> IORef [TreePath] -> IO ()
selectInvert view ioRefSelection = do
  selector <- treeViewGetSelection view
  old <- treeSelectionGetSelectedRows selector
  treeSelectionSelectAll selector
  mapM_ (treeSelectionUnselectPath selector) old
  new <- treeSelectionGetSelectedRows selector
  writeIORef ioRefSelection new

-- | Sets data of list
setListData :: TreeView -> (a -> String) -> [a] -> IO (ListStore a)
setListData view getT listData = do
  store <- listStoreNew listData
  treeViewSetModel view store
  treeViewSetHeadersVisible view False
  ren <- cellRendererTextNew
  col <- treeViewColumnNew
  treeViewColumnPackStart col ren True
  cellLayoutSetAttributes col ren store
                          $ \i -> [ cellTextMarkup := Just $ getT i ]
  treeViewAppendColumn view col
  return store

-- | Updates data of list
updateListData :: ListStore a -> [a] -> IO ()
updateListData list listData = do
  listStoreClear list
  mapM_ (listStoreAppend list) listData
