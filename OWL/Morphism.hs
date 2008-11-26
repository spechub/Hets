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
    (
     OWL_Morphism
    ,owlInclusion
    )
    where

import Common.DefaultMorphism
import OWL.Sign

type OWL_Morphism = DefaultMorphism Sign

owlInclusion :: Monad m => Sign -> Sign -> m (DefaultMorphism Sign)
owlInclusion = defaultInclusion isSubSign
