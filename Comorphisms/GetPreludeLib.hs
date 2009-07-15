{- |
Module      :  $Header$
Description :  read a prelude library for some comorphisms
Copyright   :  (c) Christian Maeder and DFKI GmbH 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

read a prelude library for some comorphisms
-}

module Comorphism.GetPreludeLib where

import Driver.AnaLib
import Driver.Options

import Proofs.TheoremHideShift

import Static.DevGraph
import Static.GTheory

import Common.Result

import Data.Maybe
import qualified Data.Map as Map

readLib :: FilePath -> IO [G_theory]
readLib fp = do
  mLib <- anaLib defaultHetcatsOpts fp
  case mLib of
    Nothing -> fail $ "library could not be read from: " ++ fp
    Just (ln, le) -> do
      let dg = lookupDGraph ln le
      return . catMaybes . Map.fold (\ ge -> case ge of
        SpecEntry (ExtGenSig _ (NodeSig n _)) ->
           if null $ outDG dg n then
               (maybeResult (computeTheory le ln n) :)
           else id
        _ -> id) [] $ globalEnv dg



