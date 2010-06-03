{-# LANGUAGE CPP #-}
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

import Driver.Options(HetcatsOpts,putIfVerbose)
import Static.DevGraph
import Common.LibName

import GUI.GraphDisplay
import GUI.GraphTypes
import GUI.ShowLibGraph(showLibGraph, mShowGraph)
#ifdef GTKGLADE
import GUI.GtkUtils(startMainLoop, stopMainLoop)
#endif

import Reactor.InfoBus (shutdown)
import HTk.Toolkit.DialogWin (useHTk)
import Util.WBFiles
import Common.UniUtils

import Data.IORef
import Control.Concurrent.MVar
import Common.Exception
import Common.ProverTools

import Interfaces.DataTypes

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
    if noWish || noUDrawGraph then
      error $ (if noWish then "wish" else "uDrawGraph") ++ " is missing"
      else do
      putIfVerbose opts 2 $ "Displaying " ++ file ++ " in a graphical window"
      putIfVerbose opts 3 "Initializing Converter"
#ifdef GTKGLADE
      eitherGTK <- try startMainLoop
      case eitherGTK of
        Right () -> return ()
        Left e -> do
          putIfVerbose opts 5 $ "Error: " ++ show e
          error $ "Can't initialize GTK."
#endif
      eitherHTK <- try initializeConverter
      (gInfo,wishInst) <- case eitherHTK of
        Right a -> return a
        Left e -> do
          putIfVerbose opts 5 $ "Error: " ++ show e
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
#ifdef GTKGLADE
      stopMainLoop
#endif
      destroy wishInst
      shutdown
  Nothing -> putIfVerbose opts 0
    "missing development graph to display in a window"
