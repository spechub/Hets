{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable 

   auxiliary functions for raw kinds
-}

module HasCASL.ClassAna where

import HasCASL.As
import HasCASL.AsUtils
import Common.Id
import HasCASL.Le
import Common.PrettyPrint
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.Result

anaClassId :: ClassId -> ClassMap -> Result Kind
anaClassId ci cMap = 
       case Map.lookup ci cMap of
            Nothing -> mkError "undeclared class" ci
            Just (ClassInfo l) -> return $ ClassKind ci $ toIntersection l []

toIntersection :: [Kind] -> [Pos] -> Kind
toIntersection l ps = case Set.toList $ mkIntersection l of
                          [] -> Intersection [] ps
                          [h] -> h
                          is -> Intersection is ps

mkIntersection :: [Kind] -> Set.Set Kind
mkIntersection = Set.unions . map ( \ k -> case k of
                                 Intersection lk _ -> mkIntersection lk
                                 _ -> Set.singleton k) 

rawKind :: Kind -> Kind
rawKind c = 
    case c of
    MissingKind -> error "rawKind"
    ClassKind _ rk -> rawKind rk
    Downset _ _ rk _ -> rawKind rk
    Intersection l _ -> if null l then c
                        else rawKind $ head l
    FunKind e k ps  -> FunKind (rawKind e) (rawKind k) ps
    ExtKind k v ps -> ExtKind (rawKind k) v ps 

checkIntersection :: Kind -> [Kind] -> [Diagnosis]
checkIntersection _ [] = []
checkIntersection k (f:r) = 
        case k == rawKind f of 
        False -> 
              Diag Error ("incompatible kind of: " ++ showPretty f "" 
                ++  "\n  for raw kind: " ++ showPretty k "")
              (posOf [f]) : checkIntersection k r
        True -> checkIntersection k r

diffKindDiag :: (PosItem a, PrettyPrint a) => 
                 a -> Kind -> Kind -> [Diagnosis]
diffKindDiag a k1 k2 = 
           [ Diag Error
              ("incompatible kind of: " ++ showPretty a "" ++ expected k1 k2)
            $ posOf [a] ]

checkKinds :: (PosItem a, PrettyPrint a) => 
              a -> Kind -> Kind -> [Diagnosis]
checkKinds p k1 k2 =
    do let k3 = rawKind k1
           k4 = rawKind k2
       if k3 == k4 then []
          else diffKindDiag p k1 k2

cyclicClassId :: ClassId -> Kind -> Bool
cyclicClassId ci k =
    case k of
           FunKind k1 k2 _ -> cyclicClassId ci k1 || cyclicClassId ci k2
           ExtKind ek _ _ -> cyclicClassId ci ek
           ClassKind cj ck -> cj == ci || cyclicClassId ci ck
           Downset _ _ dk _ -> cyclicClassId ci dk
           Intersection l _ -> any (cyclicClassId ci) l
           _ -> False
