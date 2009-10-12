{-# LANGUAGE CPP #-}
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
#if defined GTKGLADE || defined UNI_PACKAGE
  , createTextDisplay
  , infoDialog
  , errorDialog
  , warningDialog
  , questionDialog

  , fileOpenDialog
  , fileSaveDialog

  , displayTheory
  , displayTheoryWithWarning

  , progressBar
  , pulseBar
#endif
  ) where

#ifdef GTKGLADE
import GUI.GtkUtils
  ( infoDialogExt
  , errorDialogExt
  , warningDialogExt
  , questionDialogExt
  , fileSaveDialogExt
  , fileOpenDialogExt
  , listChoiceExt
  , textViewExt
  , displayTheoryExt
  , displayTheoryWithWarningExt
  , progressBarExt
  , pulseBarExt
  )
import Static.GTheory (G_theory)

-- | create a window which displays a given text
infoDialog :: String -- ^ Title
           -> String -- ^ Message
           -> IO ()
infoDialog = infoDialogExt

-- | create a window which displays a given error
errorDialog :: String -- ^ Title
            -> String -- ^ Message
            -> IO ()
errorDialog = errorDialogExt

-- | create a window which displays a given warning and ask for continue
warningDialog :: String -- ^ Title
              -> String -- ^ Message
              -> Maybe (IO ()) -- ^ Action on Ok
              -> IO Bool
warningDialog = warningDialogExt

-- | create a window which displays a given question
questionDialog :: String  -- ^ Title
               -> String  -- ^ Message
               -> Maybe (IO ()) -- ^ Action on Yes
               -> IO Bool
questionDialog = questionDialogExt

fileSaveDialog :: FilePath -- ^ Defaultname for file
               -> [(String, [String])] -- ^ Filter (name, pattern list)
               -> Maybe (FilePath -> IO ()) -- ^ Action on save
               -> IO (Maybe FilePath)
fileSaveDialog = fileSaveDialogExt

fileOpenDialog :: FilePath -- ^ Defaultname for file
               -> [(String, [String])] -- ^ Filter (name, pattern list)
               -> Maybe (FilePath -> IO ()) -- ^ Action on open
               -> IO (Maybe FilePath)
fileOpenDialog = fileOpenDialogExt

-- | displays a theory in a window
displayTheory :: String -- ^ Kind of theory
              -> String -- ^ Name of theory
              -> G_theory -- ^ Theory
              -> IO ()
displayTheory = displayTheoryExt

-- | displays a theory with warning in a window
displayTheoryWithWarning :: String -- ^ Kind of theory
                         -> String -- ^ Name of theory
                         -> String -- ^ Warning
                         -> G_theory -- ^ Theory
                         -> IO ()
displayTheoryWithWarning = displayTheoryWithWarningExt

progressBar :: String -- ^ Title
            -> String -- ^ Description
            -> IO (Double -> String -> IO (), IO ())
progressBar = progressBarExt

pulseBar :: String -- ^ Title
         -> String -- ^ Description
         -> IO (String -> IO (), IO ())
pulseBar = pulseBarExt

-- | create a window with title and list of options, return selected option
listBox :: String -- ^ Title
        -> [String] -- ^ Rows to display
        -> IO (Maybe Int) -- ^ Selected row
listBox = listChoiceExt

-- | Display some (longish) text in an uneditable, scrollable editor.
createTextDisplay :: String -- ^ Title
                  -> String -- ^ Message
                  -> IO ()
createTextDisplay t m = textViewExt t m Nothing

-- | Display some (longish) text in an uneditable, scrollable editor.
createTextSaveDisplay :: String -- ^ Title
                      -> FilePath -- ^ Filename
                      -> String -- ^ Message
                      -> IO ()
createTextSaveDisplay t f m = textViewExt t m $ Just f

-- | opens a FileDialog and saves to the selected file if Save is clicked
askFileNameAndSave :: FilePath -- ^ default filename for saving the text
                   -> String -- ^ text to be saved
                   -> IO ()
askFileNameAndSave f m = do
  fileSaveDialogExt f [] $ Just (\ f' -> writeFile f' m)
  return ()

#elif defined UNI_PACKAGE
import GUI.HTkUtils
  ( listBox
  , errorMess
  , confirmMess
  , messageMess
  , createTextSaveDisplay
  , askFileNameAndSave
  , newFileDialogStr
  , fileDialogStr
  , displayTheory
  , displayTheoryWithWarning
  , sync
  )
import qualified GUI.HTkUtils (createTextDisplay)

-- | create a window which displays a given text
infoDialog :: String -- ^ Title
           -> String -- ^ Message
           -> IO ()
infoDialog _ m = messageMess m

-- | create a window which displays a given error
errorDialog :: String -- ^ Title
            -> String -- ^ Message
            -> IO ()
errorDialog _ m = errorMess m

-- | create a window which displays a given warning and ask for continue
warningDialog :: String -- ^ Title
              -> String -- ^ Message
              -> Maybe (IO ()) -- ^ Action on Ok
              -> IO Bool
warningDialog _ m mAction = do
  ret <- confirmMess m
  case ret of
    True -> case mAction of
      Just action -> action
      Nothing -> return ()
    False -> return ()
  return ret

-- | create a window which displays a given question
questionDialog :: String  -- ^ Title
               -> String  -- ^ Message
               -> Maybe (IO ()) -- ^ Action on Yes
               -> IO Bool
questionDialog _ m mAction = do
  ret <- confirmMess m
  case ret of
    True -> case mAction of
      Just action -> action
      Nothing -> return ()
    False -> return ()
  return ret

fileOpenDialog :: FilePath -- ^ Defaultname for file
               -> [(String, [String])] -- ^ Filter (name, pattern list)
               -> Maybe (FilePath -> IO ()) -- ^ Action on open
               -> IO (Maybe FilePath)
fileOpenDialog f _ mAction = do
  evnt <- fileDialogStr "Open..." f
  mPath <- sync evnt
  case mPath of
    Just path -> case mAction of
      Just action -> action path
      Nothing -> return ()
    Nothing -> return ()
  return mPath

fileSaveDialog :: FilePath -- ^ Defaultname for file
               -> [(String, [String])] -- ^ Filter (name, pattern list)
               -> Maybe (FilePath -> IO ()) -- ^ Action on save
               -> IO (Maybe FilePath)
fileSaveDialog f _ mAction = do
  evnt <- newFileDialogStr "Save as..." f
  mPath <- sync evnt
  case mPath of
    Just path -> case mAction of
      Just action -> action path
      Nothing -> return ()
    Nothing -> return ()
  return mPath

-- | Display some (longish) text in an uneditable, scrollable editor.
createTextDisplay :: String -- ^ Title
                  -> String -- ^ Message
                  -> IO ()
createTextDisplay t m = GUI.HTkUtils.createTextDisplay t m []

-- Not implemented in HTk
progressBar :: String -- ^ Title
            -> String -- ^ Description
            -> IO (Double -> String -> IO (), IO ())
progressBar _ _ = return (\ _ _ -> return (), return ())

-- Not implemented in HTk
pulseBar :: String -- ^ Title
         -> String -- ^ Description
         -> IO (String -> IO (), IO ())
pulseBar _ _ = return (\ _ -> return (), return ())


#else
import GUI.ConsoleUtils (listBox, createTextSaveDisplay, askFileNameAndSave)
#endif
