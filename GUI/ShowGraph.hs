{-# OPTIONS -cpp #-}
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

import Driver.Options

import Syntax.AS_Library(LIB_NAME)
import Static.DevGraph

#ifdef UNI_PACKAGE
import GUI.AbstractGraphView
import GUI.ConvertDevToAbstractGraph
import InfoBus
import Events
import Destructible
import DialogWin (useHTk)
#endif


showGraph :: FilePath -> HetcatsOpts ->
             Maybe (LIB_NAME, -- filename
                    LibEnv    -- DGraphs for imported modules
                   )  -> IO ()
showGraph file opt env =
    case env of
        Just (ln, libenv) -> do
            putIfVerbose opt 2 ("Trying to display " ++ file
                                ++ " in a graphical window")
            putIfVerbose opt 3 "Initializing Converter"
#ifdef UNI_PACKAGE
            graphMem <- initializeConverter
            useHTk -- All messages are displayed in TK dialog windows
                   -- from this point on
            putIfVerbose opt 3 "Converting Graph"
            (gid, gv, _cmaps) <- convertGraph graphMem ln libenv opt
            GUI.AbstractGraphView.redisplay gid gv
            graph <- get_graphid gid gv
            sync(destroyed graph)
            InfoBus.shutdown
            exitWith ExitSuccess
#else
            fail $ "No graph display interface; " ++
              "UNI_PACKAGE option has been disabled during compilation of Hets"
#endif
        Nothing -> putIfVerbose opt 1
            ("Error: Basic Analysis is neccessary to display "
             ++ "graphs in a graphical window")
