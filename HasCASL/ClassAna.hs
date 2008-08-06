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
import qualified Data.Set as Set
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
getFunKinds :: Monad m => ClassMap -> Kind -> m (Set.Set Kind)
getFunKinds cm k = case k of
    FunKind _ _ _ _ -> return $ Set.singleton k
    ClassKind c -> case Map.lookup c cm of
         Just info -> do
             ks <- mapM (getFunKinds cm) $ Set.toList $ classKinds info
             return $ keepMinKinds cm ks
         _ -> fail $ "not a function kind '" ++ showId c "'"

-- | compute arity from a raw kind
kindArity :: RawKind -> Int
kindArity k = case k of
    ClassKind _ -> 0
    FunKind _ _ rk _ -> 1 + kindArity rk

-- | check if a class occurs in one of its super kinds
cyclicClassId :: ClassMap -> Id -> Kind -> Bool
cyclicClassId cm ci k = case k of
    FunKind _ k1 k2 _ -> cyclicClassId cm ci k1 || cyclicClassId cm ci k2
    ClassKind cj  -> cj /= universeId &&
      (cj == ci || not (Set.null $ Set.filter (cyclicClassId cm ci)
          $ classKinds $ Map.findWithDefault (error "cyclicClassId") cj cm))

-- * subkinding

-- | keep only minimal elements according to 'lesserKind'
keepMinKinds :: ClassMap -> [Set.Set Kind] -> Set.Set Kind
keepMinKinds cm = Set.fromDistinctAscList
    . keepMins (lesserKind cm) . Set.toList . Set.unions

-- | no kind of the set is lesser than the new kind
newKind :: ClassMap -> Kind -> Set.Set Kind -> Bool
newKind cm k = Set.null . Set.filter (flip (lesserKind cm) k)

-- | add a new kind to a set
addNewKind :: ClassMap -> Kind -> Set.Set Kind -> Set.Set Kind
addNewKind cm k = Set.insert k . Set.filter (not . lesserKind cm k)

lesserVariance :: Variance -> Variance -> Bool
lesserVariance v1 v2 = case v1 of
  InVar -> True
  _ -> case v2 of
         NonVar -> True
         _ -> v1 == v2

-- | revert variance
revVariance :: Variance -> Variance
revVariance v = case v of
    InVar -> NonVar
    CoVar -> ContraVar
    ContraVar -> CoVar
    NonVar -> InVar

-- | compute the minimal variance
minVariance :: Variance -> Variance -> Variance
minVariance v1 v2 = case v1 of
  NonVar -> v2
  _ -> case v2 of
         NonVar -> v1
         _ -> if v1 == v2 then v1 else InVar

-- | check subkinding (kinds with variances are greater)
lesserKind :: ClassMap -> Kind -> Kind -> Bool
lesserKind cm k1 k2 = case k1 of
    ClassKind c1 -> (case k2 of
        ClassKind c2 -> c1 == c2 || if k1 == universe then
                        False else k2 == universe
        _ -> False) ||
          case Map.lookup c1 cm of
          Just info -> not $ newKind cm k2 $ classKinds info
          _ -> False
    FunKind v1 a1 r1 _ -> case k2 of
        FunKind v2 a2 r2 _ -> lesserVariance v1 v2
            && lesserKind cm r1 r2 && lesserKind cm a2 a1
        _ -> False

-- | compare raw kinds
lesserRawKind :: RawKind -> RawKind -> Bool
lesserRawKind k1 k2 = case k1 of
    ClassKind _ -> case k2 of
        ClassKind _ -> True
        _ -> False
    FunKind v1 a1 r1 _ -> case k2 of
        FunKind v2 a2 r2 _ -> lesserVariance v1 v2
            && lesserRawKind r1 r2 && lesserRawKind a2 a1
        _ -> False

minRawKind :: Monad m => String -> RawKind -> RawKind -> m RawKind
minRawKind str k1 k2 = let err = fail $ diffKindString str k1 k2 in case k1 of
    ClassKind _ -> case k2 of
        ClassKind _ -> return $ ClassKind ()
        _ -> err
    FunKind v1 a1 r1 ps -> case k2 of
        FunKind v2 a2 r2 qs -> do
            a3 <- minRawKind str a2 a1
            r3 <- minRawKind str r1 r2
            return $ FunKind (minVariance v1 v2) a3 r3 $ appRange ps qs
        _ -> err

rawToKind :: RawKind -> Kind
rawToKind = mapKind (const universeId)

-- * diagnostic messages

-- | create message for different kinds
diffKindString :: String -> RawKind -> RawKind -> String
diffKindString a k1 k2 = "incompatible kind of: " ++ a ++
    expected (rawToKind k1) (rawToKind k2)

-- | create diagnostic for different kinds
diffKindDiag :: (GetRange a, Pretty a) =>
                a -> RawKind -> RawKind -> [Diagnosis]
diffKindDiag a k1 k2 =
   [Diag Error (diffKindString (showDoc a "") k1 k2) $ getRange a]

-- | check if raw kinds are compatible
checkKinds :: (GetRange a, Pretty a) =>
              a -> RawKind -> RawKind -> [Diagnosis]
checkKinds p k1 k2 =
    maybe (diffKindDiag p k1 k2) (const []) $ minRawKind "" k1 k2

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
    if ci == universeId then
       addDiags [mkDiag Warning "void universe class declaration" ci]
    else do
       e <- get
       let cm = classMap e
           tm = typeMap e
           tvs = localTypeVars e
       case Map.lookup ci tm of
         Just _ -> addDiags [mkDiag Error "class name already a type" ci]
         Nothing -> case Map.lookup ci tvs of
             Just _ -> addDiags
                 [mkDiag Error "class name already a type variable" ci]
             Nothing -> case Map.lookup ci cm of
                 Nothing -> do
                   addSymbol $ idToClassSymbol e ci rk
                   putClassMap $ Map.insert ci
                     (ClassInfo rk $ Set.singleton kind) cm
                 Just (ClassInfo ork superClasses) ->
                   let Result ds mk = minRawKind (showDoc ci "") rk ork
                   in case mk of
                   Nothing -> addDiags ds
                   Just nk ->
                     if cyclicClassId cm ci kind then
                        addDiags [mkDiag Error "cyclic class" ci]
                     else do
                       addSymbol $ idToClassSymbol e ci nk
                       if newKind cm kind superClasses then do
                         addDiags [mkDiag Warning "refined class" ci]
                         putClassMap $ Map.insert ci
                           (ClassInfo nk $ addNewKind cm kind superClasses) cm
                        else addDiags [mkDiag Warning "unchanged class" ci]
