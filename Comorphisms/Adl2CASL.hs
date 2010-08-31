{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  Coding a description language into CASL
Copyright   :  (c)  Stef Joosten, Christian Maeder DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt

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

-- CASL
import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.Sublogic
import CASL.Sign as C
import CASL.Simplify
import CASL.Morphism as C
import CASL.Fold
import CASL.Overload

import Common.AS_Annotation
import Common.DefaultMorphism
import Common.DocUtils
import Common.Id
import Common.ProofTree
import Common.Result
import Common.Token
import qualified Common.Lib.Rel as Rel
import Common.Lib.State

import qualified Data.Set as Set
import qualified Data.Map as Map

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
      map_sentence Adl2CASL s = return . mapSen (mapSign s)
      map_morphism Adl2CASL = mapMor
      map_symbol Adl2CASL _ = Set.singleton . mapSym
      is_model_transportable Adl2CASL = True
      has_model_expansion Adl2CASL = True
      is_weakly_amalgamable Adl2CASL = True
      isInclusionComorphism Adl2CASL = True

mapTheory :: (A.Sign, [Named Sen]) -> Result (CASLSign, [Named CASLFORMULA])
mapTheory (s, ns) = let cs = mapSign s in
  return (cs, map (mapNamed $ mapSen cs) ns)

relTypeToPred :: RelType -> PredType
relTypeToPred (RelType c1 c2) = PredType [conceptToId c1, conceptToId c2]

mapSign :: A.Sign -> CASLSign
mapSign s = (C.emptySign ())
  { sortSet = Set.fold (\ sy -> case sy of
                 Con (C i) -> Set.insert $ simpleIdToId i
                 _ -> id) Set.empty $ A.symOf s
  , sortRel = Rel.map conceptToId $ isas s
  , predMap = Map.fromList . map (\ (i, l) -> (transRelId $ idToSimpleId i, l))
      . Map.toList . Map.map (Set.map relTypeToPred) $ rels s
  }

transRelId :: Token -> Id
transRelId t@(Token s p) = simpleIdToId $
   if elem s casl_reserved_fwords then Token ("P_" ++ s) p else t

mapSen :: CASLSign -> Sen -> CASLFORMULA
mapSen sig s = case s of
  DeclProp r p -> getRelProp sig r p
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
  Rel (Sgn n t) -> idToPredSymbol (transRelId n) $ relTypeToPred t

next :: State Int Int
next = do
  i <- get
  put $ i + 1
  return i

getRelPred :: CASLSign -> Relation -> PRED_SYMB
getRelPred sig m@(Sgn t (RelType c1 c2)) = let
  ty1 = conceptToId c1
  ty2 = conceptToId c2
  i = transRelId t
  cs = filter (\ pt -> case predArgs pt of
                  [fr, to] -> leqSort sig ty1 fr && leqSort sig ty2 to
                  _ -> False)
               $ Set.toList $ Map.findWithDefault Set.empty i
               $ predMap sig
  in case cs of
       ty : _ ->
           Qual_pred_name i (toPRED_TYPE ty) $ tokPos t
       _ -> error $ "getRelPred " ++ showDoc m ""

getRelProp :: CASLSign -> Relation -> RangedProp -> CASLFORMULA
getRelProp sig r p =
  let qp@(Qual_pred_name _ (Pred_type [fr, to] _) _) = getRelPred sig r
      q = propRange p
      q1 = Var_decl [mkSimpleId "a"] fr q
      q2 = Var_decl [mkSimpleId "b"] to q
      q3 = Var_decl [mkSimpleId "c"] fr q
      t1 = toQualVar q1
      t2 = toQualVar q2
      t3 = toQualVar q3
      pAppl = Predication qp [t1, t2] q
      eqs = fr == to
  in case propProp p of
       Uni -> mkForall [q1, q2, q3]
            (Implication
             (Conjunction
              [pAppl, Predication qp [t3, t2] q] q)
             (Strong_equation t1 t3 q)
             True q) q
       Tot -> mkForall [q1] (Quantification Existential [q2] pAppl q) q
       Sur -> mkForall [q2] (Quantification Existential [q1] pAppl q) q
       Inj -> let
         q4 = Var_decl [mkSimpleId "c"] to q
         t4 = toQualVar q4
         in mkForall [q1, q2, q4]
            (Implication
             (Conjunction
              [pAppl, Predication qp [t1, t4] q] q)
             (Strong_equation t2 t4 q)
             True q) q
       Sym | eqs ->
         mkForall [q1, q2] (Equivalence pAppl (Predication qp [t2, t1] q) q) q
       Asy | eqs -> mkForall [q1, q2]
         (Implication pAppl (Negation (Predication qp [t2, t1] q) q) True q) q
       Trn | eqs -> mkForall [q1, q2, q3]
          (Implication
           (Conjunction [pAppl, Predication qp [t2, t3] q] q)
             (Predication qp [t1, t3] q)
             True q) q
       Rfx | eqs -> mkForall [q1] (Predication qp [t1, t1] q) q
       pr -> error $ "getRelProp " ++ showDoc pr ""

transRule :: CASLSign -> Rule
          -> State Int ((VAR, SORT), (VAR, SORT), CASLFORMULA)
transRule sig rule =
  let myMin v@(ta, sa) (_, sb) =
               if leqSort sig sa sb then v else
               if leqSort sig sb sa then (ta, sb) else
                   error $ "transRule.myMin " ++ showDoc (sa, sb) "\n "
                   ++ showDoc rule ""
      myVarDecl = uncurry mkVarDecl
      disjunct fs = Disjunction fs nullRange
      mkExist vs f = Quantification Existential vs f nullRange
  in case rule of
  Tm m@(Sgn (Token s p) (RelType c1 c2)) -> do
      i <- next
      j <- next
      let v1 = mkNumVar "a" i
          v2 = mkNumVar "b" j
          isI = s == "I"
          ty1' = conceptToId c1
          ty2' = conceptToId c2
          ty1 = if isI && leqSort sig ty2 ty1 then ty2' else ty1'
          ty2 = if isI && leqSort sig ty1 ty2 then ty1' else ty2'
          q1 = Qual_var v1 ty1 p
          q2 = Qual_var v2 ty2 p
      return ((v1, ty1), (v2, ty2),
        if s == "V" then True_atom p else
        if isI then
            if ty1 == ty2 then Strong_equation q1 q2 p else
                error $ "transRule.I " ++ showDoc rule ""
        else
          let qp@(Qual_pred_name _ (Pred_type [fr, to] _) _) = getRelPred sig m
          in Predication qp
            [ if ty1 == fr then q1 else Sorted_term q1 fr p
            , if ty2 == to then q2 else Sorted_term q2 to p] p)
  UnExp o e -> do
    (v1, v2@(t2, _), f) <- transRule sig e
    case o of
      Co -> return (v2, v1, f)
      Cp -> return (v1, v2, negateForm f nullRange)
      _ -> do
        k <- next
        let v@(_, s) = myMin v1 v2
            w = (t2, s)
            nf = renameVar sig v1 v $ renameVar sig v2 w f
            z = (mkNumVar "c" k, s)
            cf = mkExist [myVarDecl z]
                 $ conjunct [renameVar sig v z nf, renameVar sig w z nf]
        -- this is (and always will be) incomplete wrt to compositions
        return (v, w, disjunct
           $ [ mkStEq (toQualVar $ myVarDecl v) $ toQualVar $ myVarDecl w
             | o == K0] ++ [nf, cf])
  MulExp o es -> case es of
    [] -> error "transRule2"
    r : t -> if null t then transRule sig r else do
       (v1, v2, f1) <- transRule sig r
       (v3, v4, f2) <- transRule sig $ MulExp o t
       if elem o [Fc, Fd] then return (v1, v4,
         let v23 = myMin v2 v3
             f3 = renameVar sig v2 v23 f1
             f4 = renameVar sig v3 v23 f2
             vs = [myVarDecl v23]
             cs = [f3, f4]
         in if o == Fc then mkExist vs $ conjunct cs
              else mkForall vs (disjunct cs) nullRange)
         else do
           let v13 = myMin v1 v3
               v24 = myMin v2 v4
               f3 = renameVar sig v1 v13 $ renameVar sig v2 v24 f1
               f4 = renameVar sig v3 v13 $ renameVar sig v4 v24 f2
           return (v13, v24, case o of
             Fi -> conjunct [f3, f4]
             Fu -> disjunct [f3, f4]
             Ri -> mkImpl f3 f4
             Rr -> Implication f4 f3 False nullRange
             Re -> mkEqv f3 f4
             _ -> error "transRule,MulExp")

renameVarRecord :: CASLSign -> (VAR, SORT) -> (VAR, SORT)
                -> Record () CASLFORMULA (TERM ())
renameVarRecord sig from to = (mapRecord id)
  { foldQual_var = \ _ v ty p ->
      let (nv, nty) = if (v, ty) == from then to else (v, ty)
          qv = Qual_var nv nty p
      in if nty == ty then qv else
         if leqSort sig nty ty then Sorted_term qv ty p else
             error "renameVar"
  }

renameVar :: CASLSign -> (VAR, SORT) -> (VAR, SORT) -> CASLFORMULA
          -> CASLFORMULA
renameVar sig v = foldFormula . renameVarRecord sig v
