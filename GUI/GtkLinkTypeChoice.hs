module GUI.GtkLinkTypeChoice
  (showLinkTypeChoiceDialog)
  where

import Graphics.UI.Gtk
import Graphics.UI.Gtk.Glade

import Monad(foldM)

{-
linkTypes :: [String]
linkTypes =
  [ "globaldef"
  , "localdef"
  , "def"
  , "hidingdef"
  , "hetdef"
  , "proventhm"
  , "unproventhm"
  , "localproventhm"
  , "localunproventhm"
  , "hetproventhm"
  , "hetunproventhm"
  , "hetlocalproventhm"
  , "hetlocalunproventhm"
  , "unprovenhidingthm"
  , "provenhidingthm"
  , "reference"
  ]
-}

showLinkTypeChoiceDialog :: [String] -> ([String] -> IO ()) -> IO ()
showLinkTypeChoiceDialog linkTypes updateFunction = do
  initGUI
  Just xml <- xmlNew "GUI/GtkLinkTypeChoice.glade"
  window   <- xmlGetWidget xml castToWindow "linktypechoice"
  ok       <- xmlGetWidget xml castToButton "b_ok"
  cancel   <- xmlGetWidget xml castToButton "b_cancel"
  onDestroy window mainQuit

  onClicked cancel $ do
    widgetDestroy window

  onClicked ok $ do
    checkButtons <- mapM (\ name -> do
                            cb <- xmlGetWidget xml castToCheckButton $
                                               "cb_" ++ name
                            return (name, cb)) linkTypes
    linkTypes' <- foldM (\ selected (name, cb) -> do
                           selection <- toggleButtonGetActive cb
                           case selection of
                             True -> return $ name:selected
                             False -> return selected) [] checkButtons
    updateFunction linkTypes'
    widgetDestroy window

  widgetShowAll window
  mainGUI
