{-# OPTIONS -cpp #-}
{- |
Module      :  $Header$
Description :  cpp choice between "GUI.HTkUtils" and "GUI.ConsoleUtils"
Copyright   :  (c) C. Maeder, Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (cpp)

Utilities on top of HTk or System.IO
-}

module GUI.Utils
  ( listBox
  , createTextSaveDisplay
  , askFileNameAndSave

#if (defined GTKGLADE || defined UNI_PACKAGE)
  , infoDialog
  , errorDialog
  , warningDialog
  , questionDialog

  , displayTheory
  , displayTheoryWithWarning
#endif
  ) where

#ifdef GTKGLADE
import GUI.GtkUtils
  ( infoDialog
  , errorDialog
  , warningDialog
  , questionDialog
  , fileSaveDialog
  , listChoice
  , textView
  , displayTheory
  , displayTheoryWithWarning
  )

-- | create a window with title and list of options, return selected option
listBox :: String -- ^ Title
        -> [String] -- ^ Rows to display
        -> IO (Maybe Int) -- ^ Selected row
listBox = listChoice

-- | Display some (longish) text in an uneditable, scrollable editor.
createTextSaveDisplay :: String -- ^ Title
                      -> FilePath -- ^ Filename
                      -> String -- ^ Message
                      -> IO ()
createTextSaveDisplay t f m = textView t m f

-- | opens a FileDialog and saves to the selected file if Save is clicked
askFileNameAndSave :: String -- ^ default filename for saving the text
                   -> String -- ^ text to be saved
                   -> IO ()
askFileNameAndSave f m = do
  fileSaveDialog f [] $ Just (\ f' -> writeFile f' m)
  return ()

#elif defined UNI_PACKAGE
import GUI.HTkUtils
  ( listBox
  , createTextSaveDisplay
  , askFileNameAndSave
  , createInfoWindow
  , createInfoDisplayWithTwoButtons
  , displayTheory
  , displayTheoryWithWarning
  )
import Data.IORef

-- | create a window which displays a given text
infoDialog :: String -- ^ Title
           -> String -- ^ Message
           -> IO ()
infoDialog = createInfoWindow

-- | create a window which displays a given error
errorDialog :: String -- ^ Title
            -> String -- ^ Message
            -> IO ()
errorDialog = createInfoWindow

-- | create a window which displays a given warning and ask for continue
warningDialog :: String -- ^ Title
              -> String -- ^ Message
              -> Maybe (Bool -> IO ()) -- ^ Action on Ok
              -> IO Bool
warningDialog = questionDialog

-- | create a window which displays a given question
questionDialog :: String  -- ^ Title
               -> String  -- ^ Message
               -> Maybe (Bool -> IO ()) -- ^ Action on Yes
               -> IO Bool
questionDialog t m ma = do
  iorRet <- newIORef False
  createInfoDisplayWithTwoButtons t m "Ok"
    (do
      writeIORef iorRet True
      case ma of
        Just a -> a True
        Nothing -> return ()
    )
  ret <- readIORef iorRet
  return ret

#else
import GUI.ConsoleUtils (listBox, createTextSaveDisplay, askFileNameAndSave)
#endif
