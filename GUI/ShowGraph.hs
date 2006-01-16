{- |
Module      :  $Header$
Copyright   :  (c) Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  non-portable (Logic)

display the final graph

-}

module GUI.ShowGraph
where

import System.Exit (ExitCode(ExitSuccess), exitWith)
import Data.IORef

import Driver.Options

import Syntax.AS_Library(LIB_NAME)
import Static.DevGraph

import GUI.AbstractGraphView
import GUI.ConvertDevToAbstractGraph
import InfoBus
import Events
import Destructible
import DialogWin (useHTk)


showGraph :: FilePath -> HetcatsOpts ->
             Maybe (LIB_NAME, -- filename
                    LibEnv    -- DGraphs for imported modules
                   )  -> IO ()
showGraph file opts env = case env of
        Just (ln, libenv) ->
            showGraphAux file opts ( \ gm -> convertGraph gm ln libenv opts)
        Nothing -> putIfVerbose opts 1 $
            "Error: Basic Analysis is neccessary to display "
             ++ "graphs in a graphical window"

showGraphAux :: FilePath -> HetcatsOpts
             -> (IORef GraphMem -> IO (Descr, GraphInfo, ConversionMaps))
             -> IO ()
showGraphAux file opts convFct = do
            putIfVerbose opts 2 $ "Trying to display " ++ file
                             ++ " in a graphical window"
            putIfVerbose opts 3 "Initializing Converter"
            graphMem <- initializeConverter
            useHTk -- All messages are displayed in TK dialog windows
                   -- from this point on
            putIfVerbose opts 3 "Converting Graph"
            (gid, gv, _cmaps) <- convFct graphMem
            GUI.AbstractGraphView.redisplay gid gv
            graph <- get_graphid gid gv
            sync(destroyed graph)
            InfoBus.shutdown
            exitWith ExitSuccess
            fail $ "No graph display interface; " ++
              "UNI_PACKAGE option has been disabled during compilation of Hets"
