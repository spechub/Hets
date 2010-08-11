{- |
Module      :  $Header$
Description :  union of signature parts
Copyright   :  (c) Christian Maeder and Uni Bremen 2003-2005
License     :  GPLv2 or higher

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

merging parts of local environment
-}

module HasCASL.Merge
    ( merge
    , mergeTypeInfo
    , mergeTypeDefn
    , mergeOpInfo
    , addUnit
    , minimizeClassMap
    ) where

import Common.Id
import Common.DocUtils
import Common.Result

import HasCASL.As
import HasCASL.Le
import HasCASL.AsUtils
import HasCASL.PrintLe
import HasCASL.ClassAna
import HasCASL.TypeAna
import HasCASL.Builtin
import HasCASL.MapTerm

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe
import Control.Monad(foldM)

mergeTypeInfo :: ClassMap -> TypeInfo -> TypeInfo -> Result TypeInfo
mergeTypeInfo cm t1 t2 = do
    let o = keepMinKinds cm [otherTypeKinds t1, otherTypeKinds t2]
        s = Set.union (superTypes t1) $ superTypes t2
    k <- minRawKind "type raw kind" (typeKind t1) $ typeKind t2
    d <- mergeTypeDefn (typeDefn t1) $ typeDefn t2
    return $ TypeInfo k o s d

mergeTypeDefn :: TypeDefn -> TypeDefn -> Result TypeDefn
mergeTypeDefn d1 d2 = case (d1, d2) of
    (_, DatatypeDefn _) -> return d2
    (PreDatatype, _) -> fail "expected data type definition"
    (_, PreDatatype) -> return d1
    (NoTypeDefn, _) -> return d2
    (_, NoTypeDefn) -> return d1
    (AliasTypeDefn s1, AliasTypeDefn s2) -> do
        s <- mergeAlias s1 s2
        return $ AliasTypeDefn s
    (_, _) -> mergeA "TypeDefn" d1 d2

mergeAlias :: Type -> Type -> Result Type
mergeAlias s1 s2 = if eqStrippedType s1 s2 then return s1 else
    fail $ "wrong type" ++ expected s1 s2

mergeOpBrand :: OpBrand -> OpBrand -> OpBrand
mergeOpBrand b1 b2 = case (b1, b2) of
    (Pred, _) -> Pred
    (_, Pred) -> Pred
    (Op, _) -> Op
    (_, Op) -> Op
    _ -> Fun

mergeOpDefn :: OpDefn -> OpDefn -> Result OpDefn
mergeOpDefn d1 d2 = case (d1, d2) of
    (NoOpDefn b1, NoOpDefn b2) -> do
        let b = mergeOpBrand b1 b2
        return $ NoOpDefn b
    (SelectData c1 s, SelectData c2 _) -> do
        let c = Set.union c1 c2
        return $ SelectData c s
    (Definition b1 e1, Definition b2 e2) -> do
        d <- mergeTerm Hint e1 e2
        let b = mergeOpBrand b1 b2
        return $ Definition b d
    (NoOpDefn b1, Definition b2 e2) -> do
        let b = mergeOpBrand b1 b2
        return $ Definition b e2
    (Definition b1 e1, NoOpDefn b2) -> do
        let b = mergeOpBrand b1 b2
        return $ Definition b e1
    (ConstructData _, SelectData _ _) ->
        fail "illegal selector as constructor redefinition"
    (SelectData _ _, ConstructData _) ->
        fail "illegal constructor as selector redefinition"
    (ConstructData _, _) -> return d1
    (_, ConstructData _) -> return d2
    (SelectData _ _, _) -> return d1
    (_, SelectData _ _) -> return d2

addUnit :: ClassMap -> TypeMap -> TypeMap
addUnit cm = fromMaybe (error "addUnit") . maybeResult . mergeTypeMap cm bTypes

mergeOpInfos :: Set.Set OpInfo -> Set.Set OpInfo -> Result (Set.Set OpInfo)
mergeOpInfos s1 s2 = if Set.null s1 then return s2 else do
    let (o, os) = Set.deleteFindMin s1
        (es, us) = Set.partition ((opType o ==) . opType) s2
    s <- mergeOpInfos os us
    r <- foldM mergeOpInfo o $ Set.toList es
    return $ Set.insert r s

mergeOpInfo :: OpInfo -> OpInfo -> Result OpInfo
mergeOpInfo o1 o2 = do
    let as = Set.union (opAttrs o1) $ opAttrs o2
    d <- mergeOpDefn (opDefn o1) $ opDefn o2
    return $ OpInfo (opType o1) as d

mergeTypeMap :: ClassMap -> TypeMap -> TypeMap -> Result TypeMap
mergeTypeMap = mergeMap . mergeTypeInfo

minimizeClassMap :: ClassMap -> ClassMap
minimizeClassMap cm = Map.map (\ ci -> ci { classKinds =
                          keepMinKinds cm [classKinds ci] }) cm

merge :: Env -> Env -> Result Env
merge e1 e2 = do
    cMap <- mergeMap mergeClassInfo (classMap e1) $ classMap e2
    let clMap = minimizeClassMap cMap
    tMap <- mergeTypeMap clMap (typeMap e1) $ typeMap e2
    let tAs = filterAliases tMap
    as <- mergeMap mergeOpInfos (assumps e1) $ assumps e2
    bs <- mergeMap (\ i1 i2 -> if i1 == i2 then return i1 else
                    fail "conflicting operation for binder syntax")
         (binders e1) $ binders e2
    return initialEnv
      { classMap = clMap
      , typeMap = tMap
      , assumps = Map.map (Set.map $ mapOpInfo (id, expandAliases tAs)) as
      , binders = bs }

mergeA :: (Pretty a, Eq a) => String -> a -> a -> Result a
mergeA str t1 t2 = if t1 == t2 then return t1 else
    fail ("different " ++ str ++ expected t1 t2)

mergeTerm :: DiagKind -> Term -> Term -> Result Term
mergeTerm k t1 t2 = if t1 == t2 then return t1 else
  Result [Diag k ("different terms" ++ expected t1 t2) $ getRange t2] $ Just t2
