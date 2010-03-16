{- |
Module      :  $Header$
Description :  Transforms an OMDoc file into a development graph
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

Given an OMDoc file, we transform it to a development graph by
following also all library links and building the Environment in
a topological order.
-}

module OMDoc.Import where

import Driver.Options

import Common.Result
-- import Common.ExtSign
-- import Common.Id
import Common.LibName
-- import Common.AS_Annotation

-- import Logic.Logic
-- import Logic.Coerce
-- import Logic.Prover
-- import Logic.Grothendieck
-- import Logic.Comorphism

import Static.DevGraph
-- import Static.GTheory

-- import Data.Graph.Inductive.Graph
-- import Data.Maybe
-- import Data.List
-- import qualified Data.Map as Map
-- import qualified Data.Set as Set

--import OMDoc.DataTypes
import OMDoc.XmlInterface (xmlIn)


anaOMDocFile :: HetcatsOpts -> FilePath -> IO (Maybe (LibName, LibEnv))
anaOMDocFile opts fp = do
  putIfVerbose opts 0 $ "anaOMDocFile: Trying to import " ++ fp
  xmlString <- readFile fp
  let Result ds mOmd = xmlIn xmlString
  showDiags opts ds
  case mOmd of Just omd -> putIfVerbose opts 0 $ show $ length $ show omd
               Nothing -> putIfVerbose opts 0 $ "No omdoc!"
  return Nothing
