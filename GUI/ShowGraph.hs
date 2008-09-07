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
import Syntax.AS_Library(LIB_NAME)
import Static.DevGraph

import GUI.GraphDisplay
import GUI.GraphTypes
import GUI.ShowLibGraph
import GUI.History(initCommandHistory)
#ifdef GTKGLADE
import GUI.GtkUtils(startMainLoop, stopMainLoop)
#endif

import InfoBus
-- import Events
import Destructible
import DialogWin (useHTk)

import Data.IORef
import Control.Concurrent.MVar

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
    startMainLoop
#endif
    (gInfo,wishInst) <- initializeConverter
    useHTk -- All messages are displayed in TK dialog windows
    -- from this point on
    writeIORef (libEnvIORef gInfo) le
    ch <- (initCommandHistory file)
    let gInfo' = gInfo { gi_LIB_NAME = ln
                       , gi_hetcatsOpts = opts
                       , commandHist = ch
                       }
    showLibGraph gInfo'
    mShowGraph gInfo' ln
    takeMVar $ exitMVar gInfo'
#ifdef GTKGLADE
    stopMainLoop
#endif
    destroy wishInst
    InfoBus.shutdown
  Nothing -> putIfVerbose opts 1 $ "Error: Basic Analysis is neccessary "
    ++ "to display graphs in a graphical window"
