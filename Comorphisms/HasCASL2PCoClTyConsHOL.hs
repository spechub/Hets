{- |
Module      :  $Header$
Description :  coding out subtyping
Copyright   :  (c) C.Maeder Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Coding out subtyping in analogy to (SubPCFOL= -> PCFOL=),
   following Chap. III:3.1 of the CASL Reference Manual

The higher kinded builtin function arrow subtypes must be ignored.
-}

module Comorphisms.HasCASL2PCoClTyConsHOL (HasCASL2PCoClTyConsHOL(..)) where

import Logic.Logic
import Logic.Comorphism
import qualified Common.Lib.Rel as Rel
import qualified Data.Map as Map
import qualified Data.Set as Set
import Common.AS_Annotation
import Common.Id
import Data.List

import HasCASL.Logic_HasCASL
import HasCASL.Sublogic
import HasCASL.TypeRel
import HasCASL.As
import HasCASL.Le
import HasCASL.Merge

-- | The identity of the comorphism
data HasCASL2PCoClTyConsHOL = HasCASL2PCoClTyConsHOL deriving Show

instance Language HasCASL2PCoClTyConsHOL

instance Comorphism HasCASL2PCoClTyConsHOL
               HasCASL Sublogic
               BasicSpec Sentence SymbItems SymbMapItems
               Env Morphism Symbol RawSymbol ()
               HasCASL Sublogic
               BasicSpec Sentence SymbItems SymbMapItems
               Env Morphism Symbol RawSymbol () where
    sourceLogic HasCASL2PCoClTyConsHOL = HasCASL
    sourceSublogic HasCASL2PCoClTyConsHOL = top
    targetLogic HasCASL2PCoClTyConsHOL = HasCASL
    mapSublogic HasCASL2PCoClTyConsHOL sl = Just $ if has_sub sl then sl
        { has_sub = False
        , has_part = True
        , which_logic = max Horn $ which_logic sl
        , has_eq = True } else sl
    map_theory HasCASL2PCoClTyConsHOL = mkTheoryMapping ( \ sig ->
      let e = encodeSig sig in
      return (e, monotonicities sig ++ generateAxioms sig))
      (map_sentence HasCASL2PCoClTyConsHOL)
    map_morphism HasCASL2PCoClTyConsHOL mor = return mor
        { msource = encodeSig $ msource mor
        , mtarget = encodeSig $ mtarget mor }
      -- other components need not to be adapted!
    map_sentence HasCASL2PCoClTyConsHOL _ = return . f2Formula
    map_symbol HasCASL2PCoClTyConsHOL = Set.singleton . id
    has_model_expansion HasCASL2PCoClTyConsHOL = True
    is_weakly_amalgamable HasCASL2PCoClTyConsHOL = True

-- | Add injection, projection and membership symbols to a signature
encodeSig :: Env -> Env
encodeSig sig = let
    tm1 = typeMap sig
    tr = Rel.toSet $ typeRel tm1
    tm = addUnit (classMap sig) tm1
    injs = Set.map (mkInjOrProj True tm) tr
    projs = Set.map (mkInjOrProj False tm) tr
    in sig { assumps = Map.insert injName injs
               $ Map.insert projName projs $ assumps sig }

generateAxioms :: Env -> [Named Sentence]
generateAxioms _ = []

monotonicities :: Env -> [Named Sentence]
monotonicities _ = []

f2Formula :: Sentence -> Sentence
f2Formula = id
