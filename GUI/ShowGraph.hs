{-# OPTIONS -cpp #-}
{- |
Module      :  $Header$
Copyright   :  (c) Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (Logic)

display the final graph
-}

module GUI.ShowGraph
    (showGraph)
where

import Driver.Options
import Static.DevGraph
import Common.LibName

import GUI.GraphDisplay
import GUI.GraphTypes
import GUI.ShowLibGraph
#ifdef GTKGLADE
import GUI.GtkUtils(startMainLoop, stopMainLoop)
#endif

#ifdef UNIVERSION2
import Reactor.InfoBus (shutdown)
import HTk.Toolkit.DialogWin (useHTk)
#else
import InfoBus (shutdown)
import DialogWin (useHTk)
#endif
import Common.UniUtils

import Data.IORef
import Control.Concurrent.MVar
import Control.Exception

import Interfaces.DataTypes

showGraph :: FilePath -> HetcatsOpts ->
             Maybe (LIB_NAME, -- filename
                    LibEnv    -- DGraphs for imported modules
                   )  -> IO ()
showGraph file opts env = case env of
  Just (ln, le) -> do
    putIfVerbose opts 2 $ "Trying to display " ++ file
                     ++ " in a graphical window"
    putIfVerbose opts 3 "Initializing Converter"
#ifdef GTKGLADE
    eitherGTK <- try startMainLoop
    case eitherGTK of
      Right () -> return ()
      Left e -> do
        putIfVerbose opts 5 $ "Error: " ++ show (e::IOException)
        error $ "Cant initialize gtk."
#endif
    eitherHTK <- try initializeConverter
    (gInfo,wishInst) <- case eitherHTK of
      Right a -> return a
      Left e -> do
        putIfVerbose opts 5 $ "Error: " ++ show (e::IOException)
        error $ "Cant initialize GUI."
    
    useHTk -- All messages are displayed in TK dialog windows
    -- from this point on
    ost <- readIORef $ intState gInfo
    let nwst = case i_state ost of
                Nothing -> ost
                Just ist -> ost{ i_state = Just $ ist { i_libEnv = le
                                                      , i_ln = ln},
                                 filename = file}
    writeIORef (intState gInfo) nwst
--    ch <- (initCommandHistory file)
    let gInfo' = gInfo { gi_hetcatsOpts = opts     }
    showLibGraph gInfo'
    mShowGraph gInfo' ln
    takeMVar $ exitMVar gInfo'
#ifdef GTKGLADE
    stopMainLoop
#endif
    destroy wishInst
    shutdown
  Nothing -> putIfVerbose opts 1 $ "Error: Basic Analysis is neccessary "
    ++ "to display graphs in a graphical window"
