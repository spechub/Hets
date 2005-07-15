{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable 

analysing kinds using a class map
-}

module HasCASL.ClassAna where

import HasCASL.As
import HasCASL.AsUtils
import Common.Id
import HasCASL.Le
import Common.PrettyPrint
import qualified Common.Lib.Map as Map
import Common.Result

-- * analyse kinds

-- | check the kind and compute the raw kind 
anaKindM :: Kind -> ClassMap -> Result RawKind
anaKindM k cm = case k of
    ClassKind ci -> if k == star then return star
       else case Map.lookup ci cm of
            Just (ClassInfo rk _)  -> return rk
            Nothing -> Result [mkDiag Error "not a class" ci] $ Just star
    FunKind k1 k2 ps -> do rk1 <- anaKindM k1 cm
                           rk2 <- anaKindM k2 cm
                           return $ FunKind rk1 rk2 ps
    ExtKind ek v ps -> do rk <- anaKindM ek cm
                          return $ ExtKind rk v ps

-- | get minimal function kinds of (class) kind
getFunKinds :: Monad m => ClassMap -> Kind -> m [Kind]
getFunKinds cm k = case k of
    FunKind _ _ _ -> return [k]
    ClassKind c -> case Map.lookup c cm of
         Just (ClassInfo _ cs) -> do 
             ks <- mapM (getFunKinds cm) cs                          
             return $ keepMinKinds cm $ concat ks
         _ -> fail $ "not a function kind '" ++ showId c "'"
    ExtKind ek _ _ -> getFunKinds cm ek

-- | a list of argument kinds with result kind
getKindAppl :: ClassMap -> Kind -> [a] -> [([Kind], Kind)]
getKindAppl cm k args = if null args then [([], k)] else
    case k of 
    FunKind k1 k2 _ -> let ks = getKindAppl cm k2 (tail args)
                       in map ( \ (kargs, rk) -> (k1 : kargs, rk)) ks
    ClassKind ci -> case Map.lookup ci cm of 
        Just (ClassInfo _ ks) -> case ks of 
            [] -> error $ "getKindAppl1 " ++ show k
            _ -> concatMap (\ fk -> getKindAppl cm fk args) ks
        _ -> error $ "getKindAppl2 " ++ show k
    _ -> error $ "getKindAppl3 " ++ show k

-- | compute arity from a raw kind
kindArity :: RawKind -> Int
kindArity k = 
    case k of
    ClassKind _ -> if k == star then 1 else error "kindArity: not a raw kind"
    FunKind _ rk _ -> 1 + kindArity rk
    ExtKind ek _ _ -> kindArity ek

-- | check if a class occurs in one of its super kinds
cyclicClassId :: ClassMap -> ClassId -> Kind -> Bool
cyclicClassId cm ci k =
    case k of
           FunKind k1 k2 _ -> cyclicClassId cm ci k1 || cyclicClassId cm ci k2
           ExtKind ek _ _ -> cyclicClassId cm ci ek
           ClassKind cj  -> if k == star then False else 
                            cj == ci || case Map.lookup cj cm of 
               Nothing -> error "cyclicClassId" 
               Just info -> any (cyclicClassId cm ci) $ classKinds info

-- * subkinding

-- | keep only minimal elements
keepMins :: (a -> a -> Bool) -> [a] -> [a]
keepMins lt l = case l of
    [] -> []
    x : r -> let s = filter ( \ y -> not (lt x y)) r
                 m = keepMins lt s
              in if any ( \ y -> lt y x) s then m
                 else x : m 

-- | keep only minimal elements according to 'lesserKind'
keepMinKinds :: ClassMap -> [Kind] -> [Kind]
keepMinKinds cm = keepMins (lesserKind cm)

-- | check subkinding (kinds with variances are greater)
lesserKind :: ClassMap -> Kind -> Kind -> Bool
lesserKind cm k1 k2 = case (k1, k2) of
    (ClassKind c1,  ClassKind c2) -> c1 == c2 || if k1 == star then
          False else k2 == star || 
          case Map.lookup c1 cm of
          Just (ClassInfo _ ks) -> any ( \ k -> lesserKind cm k k2) ks
          _ -> error "lesserKind"
    (ExtKind e1 v1 _, ExtKind e2 v2 _) -> v1 == v2 && lesserKind cm e1 e2
    (_, ExtKind e2 _ _) -> lesserKind cm k1 e2
    (FunKind a1 r1 _, FunKind a2 r2 _) -> 
        lesserKind cm r1 r2 && lesserKind cm a2 a1
    _ -> False

-- | invert (or delete if false) the variance of an extended kind
invertKindVariance :: Bool -> Kind -> Kind
invertKindVariance b k = case k of
    ExtKind ek v ps -> if b then ExtKind ek (invertVariance v) ps else ek
    _ -> k
    where
  invertVariance :: Variance -> Variance
  invertVariance v = case v of
    CoVar -> ContraVar 
    ContraVar -> CoVar 

-- * diagnostic messages

-- | create message for different kinds 
diffKindDiag :: (PosItem a, PrettyPrint a) => 
                 a -> Kind -> Kind -> [Diagnosis]
diffKindDiag a k1 k2 = 
           [ Diag Error
              ("incompatible kind of: " ++ showPretty a "" ++ expected k1 k2)
            $ getRange a ]

-- | check if raw kinds are equal
checkKinds :: (PosItem a, PrettyPrint a) => 
              a -> RawKind -> RawKind -> [Diagnosis]
checkKinds p k1 k2 =
       if k1 == k2 then []
          else diffKindDiag p k1 k2
