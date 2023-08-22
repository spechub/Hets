{- |
Module      :  ./Modal/ModalSystems.hs
Copyright   :  DFKI GmbH 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

-}

-- previously generated via GeneratePatterns and utils/genTransMFormFunc.pl

module Modal.ModalSystems (transSchemaMFormula) where

import Common.AS_Annotation
import Common.Id

-- CASL
import CASL.AS_Basic_CASL

-- ModalCASL
import Modal.AS_Modal
import Modal.Print_AS ()
import Modal.Utils

import Data.Maybe (isJust)

isImpl :: FORMULA f -> Maybe (FORMULA f, FORMULA f)
isImpl form = case form of
  Relation f1 c f2 _ | c /= Equivalence -> Just (f1, f2)
  _ -> Nothing

isBoxOrDiamond :: FORMULA M_FORMULA -> Maybe (Bool, MODALITY, FORMULA M_FORMULA)
isBoxOrDiamond form = case form of
  ExtFORMULA (BoxOrDiamond b m f _) -> Just (b, m, f)
  _ -> Nothing

isPred :: FORMULA f -> Bool
isPred form = case form of
  Predication {} -> True
  _ -> False

-- matches: [](p=>q) => []p => []q
isBoxDistrImpl :: FORMULA M_FORMULA -> Maybe [MODALITY]
isBoxDistrImpl form = case isImpl form of
  Just (f1, f2) -> case (isBoxOrDiamond f1, isImpl f2) of
    (Just (True, m1, f3), Just (f4, f5)) ->
        case (isImpl f3, isBoxOrDiamond f4, isBoxOrDiamond f5) of
          (Just (p1, p2), Just (True, m2, p3), Just (True, m3, p4))
            | isPred p1 && p1 == p3 && isPred p2 && p2 == p4
            -> Just [m1, m2, m3]
          _ -> Nothing
    _ -> Nothing
  _ -> Nothing

-- matches: []p => <>p
isSerial :: FORMULA M_FORMULA -> Maybe [MODALITY]
isSerial form = case isImpl form of
  Just (f1, f2) -> case (isBoxOrDiamond f1, isBoxOrDiamond f2) of
    (Just (True, m1, p1), Just (False, m2, p2))
      | isPred p1 && p1 == p2 -> Just [m1, m2]
    _ -> Nothing
  Nothing -> Nothing

type RELPRED = TERM () -> TERM () -> CASLFORMULA

serialSen :: VAR_DECL -> VAR_DECL -> VAR_DECL -> RELPRED -> Named CASLFORMULA
serialSen v1 v2 _ relP =
    makeNamed "Serial_D"
    $ mkForall [v1] $ mkExist [v2]
    $ relP (toQualVar v1) $ toQualVar v2

-- matches: []p => p
isReflex :: FORMULA M_FORMULA -> Maybe [MODALITY]
isReflex form = case isImpl form of
  Just (f1, p1) | isPred p1 -> case isBoxOrDiamond f1 of
    Just (True, m1, p2) | p1 == p2 -> Just [m1]
    _ -> Nothing
  _ -> Nothing

reflexSen :: VAR_DECL -> VAR_DECL -> VAR_DECL -> RELPRED -> Named CASLFORMULA
reflexSen v1 _ _ relP = let t = toQualVar v1 in
    makeNamed "Reflexive_M"
    $ mkForall [v1] $ relP t t

-- matches: []p => [][]p
isTrans :: FORMULA M_FORMULA -> Maybe [MODALITY]
isTrans form = case isImpl form of
  Just (f1, f2) -> case (isBoxOrDiamond f1, isBoxOrDiamond f2) of
    (Just (True, m1, p1), Just (True, m2, f3)) | isPred p1 ->
        case isBoxOrDiamond f3 of
          Just (True, m3, p2) | p1 == p2 -> Just [m1, m2, m3]
          _ -> Nothing
    _ -> Nothing
  Nothing -> Nothing

transSen :: Bool -> VAR_DECL -> VAR_DECL -> VAR_DECL -> RELPRED
  -> Named CASLFORMULA
transSen b v1 v2 v3 relP = let
  t1 = toQualVar v1
  t2 = toQualVar v2
  t3 = toQualVar v3
  in makeNamed "Transitive_4"
    $ mkForall [v1, v2, v3] $ mkImpl
      (conjunct [relP t1 t2, relP (if b then t2 else t1) t3])
      $ relP (if b then t1 else t2) t3

isBoxDiamond :: FORMULA M_FORMULA -> Maybe (FORMULA M_FORMULA, [MODALITY])
isBoxDiamond form = case isBoxOrDiamond form of
  Just (True, m1, f) -> case isBoxOrDiamond f of
    Just (False, m2, p) -> Just (p, [m1, m2])
    _ -> Nothing
  _ -> Nothing

-- matches: p => []<>p
isSym :: FORMULA M_FORMULA -> Maybe [MODALITY]
isSym form = case isImpl form of
  Just (p1, f1) | isPred p1 -> case isBoxDiamond f1 of
    Just (p2, l) | p1 == p2 -> Just l
    _ -> Nothing
  _ -> Nothing

symSen :: VAR_DECL -> VAR_DECL -> VAR_DECL -> RELPRED -> Named CASLFORMULA
symSen v1 v2 _ relP = let
  t1 = toQualVar v1
  t2 = toQualVar v2
  in makeNamed "Symmetric_B"
    $ mkForall [v1, v2] $ mkImpl (relP t1 t2) $ relP t2 t1

-- matches: <>p => []<>p
isEuklid :: FORMULA M_FORMULA -> Maybe [MODALITY]
isEuklid form = case isImpl form of
  Just (f1, f2) -> case isBoxOrDiamond f1 of
    Just (False, m1, p1) | isPred p1 -> case isBoxDiamond f2 of
      Just (p2, l) | p1 == p2 -> Just $ m1 : l
      _ -> Nothing
    _ -> Nothing
  Nothing -> Nothing

euklidSen :: VAR_DECL -> VAR_DECL -> VAR_DECL -> RELPRED -> Named CASLFORMULA
euklidSen = transSen False

transSchemaMFormula :: ([VAR] -> TERM M_FORMULA -> TERM ())
                    -> SORT -> PRED_NAME -> [VAR]
                    -> AnModFORM -> Maybe (Named CASLFORMULA)
transSchemaMFormula mapT world rel vars anMF = case vars of
  w1 : w2 : w3 : _ -> let
    m = [ (isSerial, serialSen)
        , (isReflex, reflexSen)
        , (isTrans, transSen True)
        , (isSym, symSen)
        , (isEuklid, euklidSen) ]
    relPred t1 t2 = mkPredication
      (mkQualPred rel $ Pred_type [world, world] nullRange)
      [t1, t2]
   in case (getRLabel anMF, item anMF) of
      (_label, f) -> case isBoxDistrImpl f of
          Just l -> addTerm mapT rel (map modToTerm l) vars Nothing
          _ -> case filter (isJust . fst) $ map (\ (p, cf) -> (p f, cf)) m of
            (Just l, cf) : _ -> addTerm mapT rel (map modToTerm l) vars
               $ Just $ cf (mkVarDecl w1 world) (mkVarDecl w2 world)
                 (mkVarDecl w3 world) relPred
            _ -> Nothing
              -- was error ("Modal2CASL: unknown formula: " ++ showDoc f "")
  _ -> error "transSchemaMFormula"
