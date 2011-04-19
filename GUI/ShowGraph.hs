{-# LANGUAGE CPP #-}
{- |
Module      :  $Header$
Copyright   :  (c) Uni Bremen 2002-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (Logic)

display the final graph
-}

module GUI.ShowGraph
    (showGraph)
where

import Driver.Options (HetcatsOpts, putIfVerbose)
import Static.DevGraph
import Common.LibName

import GUI.GraphDisplay
import GUI.GraphTypes
import GUI.ShowLibGraph
#ifdef GTKGLADE
import Graphics.UI.Gtk
#endif

import Reactor.InfoBus (shutdown)
import HTk.Toolkit.DialogWin (useHTk)
import Util.WBFiles
import Common.UniUtils

import Data.IORef
import Control.Concurrent
import Control.Exception
import Control.Monad
import Common.ProverTools

import Interfaces.DataTypes

import System.Directory
import System.FilePath

-- | show development graph of a given library name in a window
showGraph :: FilePath -> HetcatsOpts -> Maybe (LibName, LibEnv) -> IO ()
showGraph file opts env = case env of
  Just (ln, le) -> do
    ws <- getWishPath
    putIfVerbose opts 3 $ "wish is: " ++ ws
    noWish <- missingExecutableInPath ws
    dv <- getDaVinciPath
    putIfVerbose opts 3 $ "uDrawGraph is: " ++ dv
    noUDrawGraph <- missingExecutableInPath dv
    home <- getHomeDirectory
    let uDrawFile = home </> ".uDrawGraph3.1.1"
    hasUDrawFile <- doesFileExist uDrawFile
    unless hasUDrawFile $ do
       putIfVerbose opts 2 $ "creating file " ++ uDrawFile
       writeFile uDrawFile ""
    if noWish || noUDrawGraph then
      error $ (if noWish then "wish" else "uDrawGraph") ++ " is missing"
      else do
      putIfVerbose opts 2 $ "Displaying " ++ file ++ " in a graphical window"
      putIfVerbose opts 3 "Initializing Converter"
      let thr = workThread file opts ln le
#ifdef GTKGLADE
      eitherGTK <- try unsafeInitGUIForThreadedRTS
      _ <- forkIO thr
      case eitherGTK of
        Right _ -> return ()
        Left e -> do
          putIfVerbose opts 5 $ "Error: " ++ show (e :: SomeException)
          error $ "Can't initialize GTK."
      mainGUI
#else
      thr
#endif
      shutdown
  Nothing -> putIfVerbose opts 0
    "missing development graph to display in a window"

workThread :: FilePath -> HetcatsOpts -> LibName -> LibEnv -> IO ()
workThread file opts ln le = do
        eitherHTK <- try initializeConverter
        (gInfo, wishInst) <- case eitherHTK of
          Right a -> return a
          Left e -> do
            putIfVerbose opts 5 $ "Error: " ++ show (e :: SomeException)
            error "Can't initialize GUI (wish)."
        useHTk -- use TK from this point on
        ost <- readIORef $ intState gInfo
        let nwst = case i_state ost of
              Nothing -> ost
              Just ist -> ost
                { i_state = Just ist
                    { i_libEnv = le
                    , i_ln = ln }
                , filename = file }
        writeIORef (intState gInfo) nwst
        let gInfo' = gInfo
              { hetcatsOpts = opts
              , libName = ln }
        showLibGraph gInfo'
        mShowGraph gInfo' ln
        takeMVar $ exitMVar gInfo'
        closeOpenWindows gInfo'
        destroy wishInst
#ifdef GTKGLADE
        postGUISync mainQuit
#endif
