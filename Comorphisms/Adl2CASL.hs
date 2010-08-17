{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  Coding a description language into CASL
Copyright   :  (c)  Stef Joosten, Christian Maeder DFKI GmbH 2010
License     :  GPLv2 or higher

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

The translating comorphism from Adl to CASL.
-}

module Comorphisms.Adl2CASL
    ( Adl2CASL (..)
    ) where

import Logic.Logic
import Logic.Comorphism

-- Adl
import Adl.Logic_Adl as A
import Adl.As
import Adl.Sign as A
import Adl.StatAna

-- CASL
import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.Sublogic
import CASL.Sign as C
import CASL.Simplify
import CASL.Morphism as C
import CASL.Fold

import Common.AS_Annotation
import Common.DefaultMorphism
import Common.DocUtils
import Common.Id
import Common.ProofTree
import Common.Result
import qualified Common.Lib.Rel as Rel
import Common.Lib.State

import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Maybe

-- | lid of the morphism
data Adl2CASL = Adl2CASL deriving Show

instance Language Adl2CASL -- default is ok

instance Comorphism Adl2CASL
    Adl
    ()
    Context
    Sen
    ()
    ()
    A.Sign
    A.Morphism
    A.Symbol
    A.RawSymbol
    ProofTree
    CASL
    CASL_Sublogics
    CASLBasicSpec
    CASLFORMULA
    SYMB_ITEMS
    SYMB_MAP_ITEMS
    CASLSign
    CASLMor
    C.Symbol
    C.RawSymbol
    ProofTree
    where
      sourceLogic Adl2CASL = Adl
      sourceSublogic Adl2CASL = ()
      targetLogic Adl2CASL = CASL
      mapSublogic Adl2CASL _ = Just $ caslTop
        { has_part = False
        , sub_features = LocFilSub
        , cons_features = NoSortGen }
      map_theory Adl2CASL = mapTheory
      map_sentence Adl2CASL s = return . mapSen s
      map_morphism Adl2CASL = mapMor
      map_symbol Adl2CASL _ = Set.singleton . mapSym
      is_model_transportable Adl2CASL = True
      has_model_expansion Adl2CASL = True
      is_weakly_amalgamable Adl2CASL = True
      isInclusionComorphism Adl2CASL = True

mapTheory :: (A.Sign, [Named Sen]) -> Result (CASLSign, [Named CASLFORMULA])
mapTheory (s, ns) = return (mapSign s, map (mapNamed $ mapSen s) ns)

relTypeToPred :: RelType -> PredType
relTypeToPred (RelType c1 c2) = PredType [conceptToId c1, conceptToId c2]

mapSign :: A.Sign -> CASLSign
mapSign s = (C.emptySign ())
  { sortSet = Set.fold (\ sy -> case sy of
                 Con (C i) -> Set.insert $ simpleIdToId i
                 _ -> id) Set.empty $ A.symOf s
  , sortRel = Rel.map conceptToId $ isas s
  , predMap = Map.map (Set.map relTypeToPred) $ rels s
  }

mapSen :: A.Sign -> Sen -> CASLFORMULA
mapSen sig s = case s of
  DeclProp _ p -> True_atom $ getRange p
  Assertion _ r ->
    let ((v1, s1), (v2, s2), f) = evalState (transRule sig r) 1 in
    mkForall [mkVarDecl v1 s1, mkVarDecl v2 s2] f nullRange

-- | Translation of morphisms
mapMor :: A.Morphism -> Result CASLMor
mapMor mor = return $ embedMorphism ()
    (mapSign $ domOfDefaultMorphism mor) $ mapSign $ codOfDefaultMorphism mor

mapSym :: A.Symbol -> C.Symbol
mapSym s = case s of
  Con c -> idToSortSymbol $ conceptToId c
  Rel (Sgn n t) -> idToPredSymbol (simpleIdToId n) $ relTypeToPred t

next :: State Int Int
next = do
  i <- get
  put $ i + 1
  return i

transRule :: A.Sign -> Rule -> State Int ((VAR, SORT), (VAR, SORT), CASLFORMULA)
transRule sig rule = case rule of
  Tm (Sgn t@(Token s p) (RelType c1 c2)) -> do
      i <- next
      j <- next
      let v1 = mkNumVar "a" i
          v2 = mkNumVar "b" j
          isI = s == "I"
          isaRel = isas sig
          mc = if isI then compatible isaRel c1 c2 else Nothing
          ty1 = conceptToId $ fromMaybe c1 mc
          ty2 = conceptToId $ fromMaybe c2 mc
          q1 = Qual_var v1 ty1 p
          q2 = Qual_var v2 ty2 p
          cs = filter (\ (RelType fr to) -> isSubConcept isaRel c1 fr
                           && isSubConcept isaRel c2 to)
               $ Set.toList $ Map.findWithDefault Set.empty (simpleIdToId t)
               $ rels sig
      return ((v1, ty1), (v2, ty2),
        if s == "V" then True_atom p else
        if isI then
            if isJust mc then Strong_equation q1 q2 p else
                error $ "transRule1: " ++ showDoc rule ""
        else case cs of
          [] -> error $ "transRule4: " ++ showDoc rule ""
          ty@(RelType fr to) : _ -> Predication
            (Qual_pred_name (simpleIdToId t)
             (toPRED_TYPE $ relTypeToPred ty) p)
            [ if c1 == fr then q1 else Sorted_term q1 (conceptToId fr) p
            , if c2 == to then q2 else Sorted_term q2 (conceptToId to) p] p)
  UnExp o e -> do
    (v1, v2, f1) <- transRule sig e
    case o of
      Co -> return (v2, v1, f1)
      Cp -> return (v1, v2, negateForm f1 nullRange)
      _ -> return (v2, v1, f1)
  MulExp o es -> case es of
    [] -> error "transRule2"
    r : t -> if null t then transRule sig r else do
       (v1@(t1, s1), v2@(t2, s2), f1) <- transRule sig r
       (v3, v4, f2) <- transRule sig $ MulExp o t
       case o of
         Fc -> return (v1, v4, Quantification Existential [mkVarDecl t2 s2]
                (conjunct [f1, renameVar v3 v2 f2]) nullRange)
         Fd -> return (v3, v2, Quantification Universal [mkVarDecl t1 s1]
                (Disjunction [f1, renameVar v4 v1 f2] nullRange) nullRange)
         _ -> do
           let f3 = renameVar v3 v1 $ renameVar v4 v2 f2
           return (v1, v2, case o of
             Fi -> conjunct [f1, f3]
             Fu -> Disjunction [f1, f3] nullRange
             Ri -> mkImpl f1 f3
             Rr -> Implication f3 f1 False nullRange
             Re -> mkEqv f1 f3
             _ -> error "transRule3")

renameVarRecord :: (VAR, SORT) -> (VAR, SORT)
                -> Record () CASLFORMULA (TERM ())
renameVarRecord from to = (mapRecord id)
  { foldQual_var = \ _ v ty p ->
      let (nv, nty) = if (v, ty) == from then to else (v, ty)
          qv = Qual_var nv nty p
      in if nty == ty then qv else
          Sorted_term qv ty p -- check nty is smaller than ty
  }

renameVar :: (VAR, SORT) -> (VAR, SORT) -> CASLFORMULA -> CASLFORMULA
renameVar v = foldFormula . renameVarRecord v
