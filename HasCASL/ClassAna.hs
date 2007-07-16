{- |
Module      :  $Header$
Description :  analyse kinds using a class map
Copyright   :  (c) Christian Maeder and Uni Bremen 2003-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

analyse kinds using a class map
-}

module HasCASL.ClassAna where

import HasCASL.As
import HasCASL.AsUtils
import HasCASL.PrintAs ()
import Common.Id
import HasCASL.Le
import qualified Data.Map as Map
import Common.Lib.State
import Common.Result
import Common.DocUtils
import Common.Utils

-- * analyse kinds

-- | check the kind and compute the raw kind
anaKindM :: Kind -> ClassMap -> Result RawKind
anaKindM k cm = case k of
    ClassKind ci -> if k == universe then return rStar
       else case Map.lookup ci cm of
            Just (ClassInfo rk _)  -> return rk
            Nothing -> Result [mkDiag Error "not a class" ci] $ Just rStar
    FunKind v k1 k2 ps -> do
        rk1 <- anaKindM k1 cm
        rk2 <- anaKindM k2 cm
        return $ FunKind v rk1 rk2 ps

-- | get minimal function kinds of (class) kind
getFunKinds :: Monad m => ClassMap -> Kind -> m [Kind]
getFunKinds cm k = case k of
    FunKind _ _ _ _ -> return [k]
    ClassKind c -> case Map.lookup c cm of
         Just (ClassInfo _ cs) -> do
             ks <- mapM (getFunKinds cm) cs
             return $ keepMinKinds cm $ concat ks
         _ -> fail $ "not a function kind '" ++ showId c "'"

-- | compute arity from a raw kind
kindArity :: RawKind -> Int
kindArity k =
    case k of
    ClassKind _ -> 0
    FunKind _ _ rk _ -> 1 + kindArity rk

-- | check if a class occurs in one of its super kinds
cyclicClassId :: ClassMap -> Id -> Kind -> Bool
cyclicClassId cm ci k =
    case k of
           FunKind _ k1 k2 _ ->
               cyclicClassId cm ci k1 || cyclicClassId cm ci k2
           ClassKind cj  -> if k == universe then False else
                            cj == ci || case Map.lookup cj cm of
               Nothing -> error "cyclicClassId"
               Just info -> any (cyclicClassId cm ci) $ classKinds info

-- * subkinding

-- | keep only minimal elements according to 'lesserKind'
keepMinKinds :: ClassMap -> [Kind] -> [Kind]
keepMinKinds cm = keepMins (lesserKind cm)

-- | check subkinding (kinds with variances are greater)
lesserKind :: ClassMap -> Kind -> Kind -> Bool
lesserKind cm k1 k2 = case k1 of
    ClassKind c1 -> (case k2 of
        ClassKind c2 -> c1 == c2 || if k1 == universe then
                        False else k2 == universe
        _ -> False) ||
          case Map.lookup c1 cm of
          Just (ClassInfo _ ks) -> any ( \ k -> lesserKind cm k k2) ks
          _ -> False
    FunKind v1 a1 r1 _ -> case k2 of
        FunKind v2 a2 r2 _ -> (case v2 of
            InVar -> True
            _ -> v1 == v2) && lesserKind cm r1 r2 && lesserKind cm a2 a1
        _ -> False

rawToKind :: RawKind -> Kind
rawToKind = mapKind (const universeId)

-- * diagnostic messages

-- | create message for different kinds
diffKindDiag :: (PosItem a, Pretty a) =>
                 a -> RawKind -> RawKind -> [Diagnosis]
diffKindDiag a k1 k2 =
    [ Diag Error ("incompatible kind of: " ++ showDoc a "" ++
                  expected (rawToKind k1) (rawToKind k2)) $ getRange a ]

-- | check if raw kinds are equal
checkKinds :: (PosItem a, Pretty a) =>
              a -> RawKind -> RawKind -> [Diagnosis]
checkKinds p k1 k2 =
       if k1 == k2 then []
          else diffKindDiag p k1 k2

-- | analyse class decls
anaClassDecls :: ClassDecl -> State Env ClassDecl
anaClassDecls (ClassDecl cls k ps) =
    do cm <- gets classMap
       let Result ds (Just rk) = anaKindM k cm
       addDiags ds
       let ak = if null ds then k else universe
       mapM_ (addClassDecl rk ak) cls
       return $ ClassDecl cls ak ps

-- | store a class
addClassDecl :: RawKind -> Kind -> Id -> State Env ()
-- check with merge
addClassDecl rk kind ci =
    if showId ci "" == typeUniverseS then
       addDiags [mkDiag Warning "void universe class declaration" ci]
    else do
       cm <- gets classMap
       tm <- gets typeMap
       tvs <- gets localTypeVars
       case Map.lookup ci tm of
         Just _ -> addDiags [mkDiag Error "class name already a type" ci]
         Nothing -> do
           case Map.lookup ci tvs of
             Just _ ->
               addDiags [mkDiag Error "class name already a type variable" ci]
             Nothing -> do
               case Map.lookup ci cm of
                 Nothing ->
                   putClassMap $ Map.insert ci (ClassInfo rk [kind]) cm
                 Just (ClassInfo ork superClasses) -> do
                   let ds = checkKinds ci rk ork
                   addDiags ds
                   if null ds then
                     if cyclicClassId cm ci kind then
                        addDiags [mkDiag Error "cyclic class" ci]
                     else if any (\ k -> lesserKind cm k kind) superClasses
                        then addDiags [mkDiag Warning "unchanged class" ci]
                        else do addDiags [mkDiag Hint
                                         "refined class" ci]
                                putClassMap $ Map.insert ci
                                    (ClassInfo ork $ keepMinKinds cm $
                                               kind : superClasses) cm
                     else return ()
