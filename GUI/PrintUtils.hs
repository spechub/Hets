{- |
Module      :  $Header$
Description :  Pretty printing functions.
Copyright   :  (c) Rainer Grabbe 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  rainer25@informatik.uni-bremen.de
Stability   :  provisional
Portability :  needs POSIX

Pretty printing functions used by GUI.GenericATP.
-}

module GUI.PrintUtils where

import Logic.Prover

import Common.Doc
import qualified Data.Map as Map

import Interfaces.GenericATPState

-- * pretty printing functions

{- |
  Pretty printing of prover configuration.
-}
printCfgText :: Map.Map ATPIdentifier (GenericConfig proof_tree)
             -> Doc -- ^ prover configuration
printCfgText mp = text "* Configuration *" $+$ dc
             $++$ text "* Results *" $+$ dr
  where
  (dc, dr) = Map.foldWithKey (\ k cfg (dCfg, dRes) ->
      let r = proof_status cfg
      in
      ((quotes (text k) <+> equals <+> specBraces (
          text "goalStatus" <+> equals <+>
                            (text.show.goalStatus) r <> comma
          $+$ text "timeLimitExceeded" <+> equals <+>
                            (text.show.timeLimitExceeded) cfg <> comma
          $+$ text "timeUsed" <+> equals <+>
                            (text.show.timeUsed) cfg
          $+$ text "tacticScript" <+> equals <+>
                            (text.show.tacticScript) r
          ) $+$ dCfg),
       (text "Output of goal" <+> quotes (text k) <> colon
            $+$ vcat (map text $ resultOutput cfg)
          $++$ dRes)))
    (empty, empty) mp
