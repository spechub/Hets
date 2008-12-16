{- |
Module      :  $Header$
Description :  OWL Morphisms
Copyright   :  (c) Dominik Luecke, 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Morphisms for OWL
-}

module OWL.Morphism
  ( OWL_Morphism
  , owlInclusion
  , cogeneratedSign
  ) where


import OWL.AS
import OWL.Sign
import OWL.StaticAnalysis

import Common.DefaultMorphism
import Common.Result
import Common.Lib.State

import qualified Data.Set as Set
import Control.Monad

type OWL_Morphism = DefaultMorphism Sign

owlInclusion :: Monad m => Sign -> Sign -> m (DefaultMorphism Sign)
owlInclusion = defaultInclusion isSubSign

cogeneratedSign :: Set.Set Entity -> Sign -> Result OWL_Morphism
cogeneratedSign s sign =
  let sig2 = execState (mapM_ (modEntity Set.delete) $ Set.toList s) sign
  in owlInclusion sig2 sign

