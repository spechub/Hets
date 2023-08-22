{- |
Module      :  ./HasCASL/AsToLe.hs
Description :  final static analysis
Copyright   :  (c) Christian Maeder and Uni Bremen 2003-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

conversion from As to Le
-}

module HasCASL.AsToLe where

import HasCASL.As
import HasCASL.Le
import HasCASL.ClassAna
import HasCASL.VarDecl
import HasCASL.Unify
import HasCASL.OpDecl
import HasCASL.TypeAna
import HasCASL.TypeDecl
import HasCASL.Builtin
import HasCASL.PrintLe
import HasCASL.Merge

import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Id
import Common.Result
import Common.ExtSign
import Common.Prec
import Common.Lib.State

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe

-- * extract predicate ids from As for mixfix analysis

type Ids = Set.Set Id

unite :: [Ids] -> Ids
unite = Set.unions

idsOfBasicSpec :: BasicSpec -> Ids
idsOfBasicSpec (BasicSpec l) = unite $ map (idsOfBasicItem . item) l

idsOfBasicItem :: BasicItem -> Ids
idsOfBasicItem bi = case bi of
    SigItems i -> idsOfSigItems i
    ClassItems _ l _ -> unite $ map (idsOfClassItem . item) l
    GenItems l _ -> unite $ map (idsOfSigItems . item) l
    Internal l _ -> unite $ map (idsOfBasicItem . item) l
    _ -> Set.empty

idsOfClassItem :: ClassItem -> Ids
idsOfClassItem (ClassItem _ l _) = unite $ map (idsOfBasicItem . item) l

idsOfSigItems :: SigItems -> Ids
idsOfSigItems si = case si of
    TypeItems {} -> Set.empty
    OpItems b l _ -> unite $ map (idsOfOpItem b . item) l

idsOfOpItem :: OpBrand -> OpItem -> Ids
idsOfOpItem b oi = let
    stripCompound (PolyId (Id ts _ ps) _ _) = Id ts [] ps
    getPolyId (PolyId i _ _) = i
    in case oi of
    OpDecl os _ _ _ -> case b of
        Pred -> Set.union (Set.fromList $ map getPolyId os) $ Set.fromList
                $ map stripCompound os
        _ -> Set.empty
    OpDefn p _ _ _ _ -> case b of
        Pred -> Set.fromList [getPolyId p, stripCompound p]
        _ -> Set.empty

-- * basic analysis

-- | basic analysis
basicAnalysis :: (BasicSpec, Env, GlobalAnnos) ->
                 Result (BasicSpec, ExtSign Env Symbol, [Named Sentence])
basicAnalysis (b, e, ga) =
    let (nb, ne) = runState (anaBasicSpec ga b) e
        in Result (reverse $ envDiags ne) $
           Just (nb, ExtSign (cleanEnv ne) $ declSymbs ne,
                 reverse $ sentences ne)

-- | is the first argument a subsignature of the second?
isSubEnv :: Env -> Env -> Bool
isSubEnv e1 e2 =
  let c2 = classMap e2
      cm = addCpoMap c2
      t2 = typeMap e2
      tm = addUnit cm t2
      expTy = expand tm . opType
  in Map.isSubmapOfBy (\ (ClassInfo _ k1) (ClassInfo _ k2) ->
       Set.null $ Set.filter
         (\ k -> Set.null $ Set.filter (flip (lesserKind cm) k) k2) k1)
     (classMap e1) c2
     && Map.isSubmapOfBy (\ ti1 ti2 -> let
        k1 = otherTypeKinds ti1
        k2 = otherTypeKinds ti2
        in Set.null $ Set.filter (\ k -> Set.null $
                  Set.filter (flip (lesserKind cm) k) k2) k1)
     (typeMap e1) (typeMap e2)
     && Map.isSubmapOfBy (\ s1 s2 ->
         all (\ t -> any (instScheme tm 1 (expTy t) . expTy)
             $ Set.toList s2)
         $ Set.toList s1) (assumps e1) (assumps e2)

-- | compute difference of signatures
diffEnv :: Env -> Env -> Env
diffEnv e1 e2 = let
    tm = typeMap e2
    cm = diffClassMap (classMap e1) $ classMap e2
    acm = addClassMap (classMap e1) $ classMap e2
    in initialEnv
       { classMap = cm
       , typeMap = diffTypeMap acm (typeMap e1) tm
       , assumps = Map.differenceWith diffAss (assumps e1) $ assumps e2
       , binders = Map.differenceWith
           (\ i1 i2 -> if i1 == i2 then Nothing else Just i1)
           (binders e1) $ binders e2 }

-- | compute difference of operations
diffAss :: Set.Set OpInfo -> Set.Set OpInfo
        -> Maybe (Set.Set OpInfo)
diffAss s1 s2 =
    let s3 = Set.difference s1 s2 in
        if Set.null s3 then Nothing else Just s3

-- | clean up finally accumulated environment
cleanEnv :: Env -> Env
cleanEnv e = delPreDefs initialEnv
             { classMap = classMap e
             , typeMap = typeMap e
             , assumps = assumps e
             , binders = binders e }

-- | analyse basic spec
anaBasicSpec :: GlobalAnnos -> BasicSpec -> State Env BasicSpec
anaBasicSpec ga b@(BasicSpec l) = do
    e <- get
    let newAs = assumps e
        preds = Map.keysSet $ Map.filter (not . Set.null . Set.filter ( \ oi ->
                                 case opDefn oi of
                                 NoOpDefn Pred -> True
                                 Definition Pred _ -> True
                                 _ -> False)) newAs
        newPreds = idsOfBasicSpec b
        rels = Set.union preds newPreds
        newGa = addBuiltins ga
        precs = mkPrecIntMap $ prec_annos newGa
        Result _ (Just ne) = merge preEnv e
    put ne { preIds = (precs, rels), globAnnos = newGa }
    ul <- mapAnM anaBasicItem l
    return $ BasicSpec ul

-- | analyse basic item
anaBasicItem :: BasicItem -> State Env BasicItem
anaBasicItem bi = case bi of
    SigItems i -> fmap SigItems $ anaSigItems Loose i
    ClassItems inst l ps -> do
       ul <- mapAnM (anaClassItem inst) l
       return $ ClassItems inst ul ps
    GenVarItems l ps -> do
       ul <- mapM (anaddGenVarDecl True) l
       return $ GenVarItems (catMaybes ul) ps
    ProgItems l ps -> do
       ul <- mapAnMaybe anaProgEq l
       return $ ProgItems ul ps
    FreeDatatype l ps -> do
       al <- mapAnMaybe ana1Datatype l
       tys <- mapM (dataPatToType . item) al
       ul <- mapAnMaybe (anaDatatype Free tys) al
       addDataSen tys
       return $ FreeDatatype ul ps
    GenItems l ps -> do
       ul <- mapAnM (anaSigItems Generated) l
       return $ GenItems ul ps
    AxiomItems decls fs ps -> do
       tm <- gets localTypeVars -- save type map
       vs <- gets localVars -- save vars
       ds <- mapM (anaddGenVarDecl True) decls
       ts <- mapM anaFormula fs
       e <- get
       putLocalVars vs -- restore
       putLocalTypeVars tm -- restore
       let newFs = catMaybes ts
           newDs = catMaybes ds
           sens = map ( \ (_, f) -> makeNamedSen $ replaceAnnoted (Formula
                                $ mkEnvForall e (item f) ps) f) newFs
       appendSentences sens
       return $ AxiomItems newDs (map fst newFs) ps
    Internal l ps -> do
       ul <- mapAnM anaBasicItem l
       return $ Internal ul ps

-- | analyse sig items
anaSigItems :: GenKind -> SigItems -> State Env SigItems
anaSigItems gk si = case si of
    TypeItems inst l ps -> do
       ul <- anaTypeItems gk l
       return $ TypeItems inst ul ps
    OpItems b l ps -> do
       ul <- mapM (anaOpItem b) l
       let al = foldr (\ i -> case item i of
                    Nothing -> id
                    Just v -> (replaceAnnoted v i :)) [] ul
       return $ OpItems b al ps

-- | analyse a class item
anaClassItem :: Instance -> ClassItem -> State Env ClassItem
anaClassItem _ (ClassItem d l ps) = do
       cd <- anaClassDecls d
       ul <- mapAnM anaBasicItem l
       return $ ClassItem cd ul ps
