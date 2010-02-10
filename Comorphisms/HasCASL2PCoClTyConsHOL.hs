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
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Common.Lib.Rel as Rel
import Common.Id

import HasCASL.Logic_HasCASL
import HasCASL.Sublogic
import HasCASL.TypeRel
import HasCASL.As
import HasCASL.AsUtils
import HasCASL.Le
import HasCASL.FoldTerm
import HasCASL.Builtin
import HasCASL.Unify (getTypeOf)

-- | The identity of the comorphism
data HasCASL2PCoClTyConsHOL = HasCASL2PCoClTyConsHOL deriving Show

instance Language HasCASL2PCoClTyConsHOL where
  language_name HasCASL2PCoClTyConsHOL = "HasCASL2HasCASLNoSubtypes"

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
        , has_polymorphism = True
        , which_logic = max Horn $ which_logic sl
        , has_eq = True } else sl
    map_theory HasCASL2PCoClTyConsHOL = mkTheoryMapping
      (\ sig -> return (encodeSig sig, monos sig ++ subtAxioms (typeMap sig)))
      (map_sentence HasCASL2PCoClTyConsHOL)
    map_morphism HasCASL2PCoClTyConsHOL mor = return mor
        { msource = encodeSig $ msource mor
        , mtarget = encodeSig $ mtarget mor }
      -- other components need not to be adapted!
    map_sentence HasCASL2PCoClTyConsHOL _ = return . f2Formula
    map_symbol HasCASL2PCoClTyConsHOL _ = Set.singleton . id
    has_model_expansion HasCASL2PCoClTyConsHOL = True
    is_weakly_amalgamable HasCASL2PCoClTyConsHOL = True

-- | Add injection and projection symbols to a signature, remove supersorts
encodeSig :: Env -> Env
encodeSig sig = let
    tm1 = typeMap sig
    injMap = Map.insert injName (mkInjOrProj FunArr) $ assumps sig
    projMap = Map.insert projName (mkInjOrProj PFunArr) injMap
    subtRelMap = Map.insert subtRelName subtRel projMap
    in if Rel.null $ typeRel tm1 then sig else sig
           { assumps = subtRelMap
           , typeMap = Map.map ( \ ti -> ti { superTypes = Set.empty } ) tm1 }

f2Formula :: Sentence -> Sentence
f2Formula s = case s of
    Formula trm -> Formula $ t2term trm
    _ -> s

t2term :: Term -> Term
t2term = foldTerm mapRec
    { foldTypedTerm = \ (TypedTerm trm _ _ _) ntrm q ty ps ->
      case getTypeOf trm of
        Nothing -> TypedTerm ntrm q ty ps -- assume this to be the exact type
        Just sty -> if eqStrippedType ty sty
          then if q == InType then unitTerm trueId ps else ntrm
          else let
            prTrm = mkTerm projName (mkInjOrProjType PFunArr) [sty, ty] ps ntrm
          in case q of
            InType -> mkTerm defId defType [ty] ps prTrm
            AsType -> TypedTerm prTrm Inferred ty ps
            _ -> let
              rty = case getTypeAppl ty of
                      (TypeName l _ _, [lt]) | l == lazyTypeId -> lt
                      _ -> ty
              -- not not create injections into lazy types
              -- (via strippedType all functions arrows became partial)
              rtrm = mkTerm injName (mkInjOrProjType FunArr) [sty, rty] ps ntrm
              in TypedTerm rtrm q ty ps }
