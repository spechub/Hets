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
    (showGraph)
where

import Driver.Options

import Syntax.AS_Library(LIB_NAME)

import Static.DevGraph

import GUI.GraphDisplay
import GUI.GraphTypes
import GUI.ShowLibGraph

import InfoBus
import Events
import Destructible
import DialogWin (useHTk)


showGraph :: FilePath -> HetcatsOpts ->
             Maybe (LIB_NAME, -- filename
                    LibEnv    -- DGraphs for imported modules
                   )  -> IO ()
showGraph file opts env = case env of
  Just (ln, le) ->
    showGraphAux file opts ln le -- "development graph"
  Nothing -> putIfVerbose opts 1 $ "Error: Basic Analysis is neccessary "
    ++ "to display graphs in a graphical window"

showGraphAux :: FilePath -> HetcatsOpts -> LIB_NAME -> LibEnv -> IO ()
showGraphAux file opts ln le = do
  putIfVerbose opts 2 $ "Trying to display "++file++" in a graphical window"
  putIfVerbose opts 3 "Initializing Converter"
  (gInfo,wishInst) <- initializeConverter
  useHTk -- All messages are displayed in TK dialog windows
  -- from this point on
  gInfo' <- setGInfo gInfo ln le opts          
  graph <- showLibGraph gInfo'
  mShowGraph gInfo' ln
  sync(destroyed graph)
  destroy wishInst
  InfoBus.shutdown
