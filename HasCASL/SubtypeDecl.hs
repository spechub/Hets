{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

analyse subtype decls
-}

module HasCASL.SubtypeDecl
    ( anaKind
    , addSuperType
    , addAliasType
    ) where

import Common.Id
import Common.Lib.State
import qualified Data.Set as Set
import qualified Data.Map as Map
import Common.Result

import HasCASL.As
import HasCASL.AsUtils
import HasCASL.Le
import HasCASL.TypeAna
import HasCASL.ClassAna
import HasCASL.Unify
import HasCASL.VarDecl

-- | lifted 'anaKindM'
anaKind :: Kind -> State Env RawKind
anaKind k = do
    mrk <- fromResult $ anaKindM k . classMap
    case mrk of
      Nothing -> error "anaKind"
      Just rk -> return rk

etaReduceAux :: ([TypeArg], [TypeArg], [Type])
             -> ([TypeArg], [TypeArg], [Type])
etaReduceAux p = case p of
    (ks, nA : rAs , tA : rArgs) | typeArgToType nA == tA ->
              etaReduceAux (nA : ks, rAs, rArgs)
    _ -> p

etaReduce :: Kind -> [TypeArg] -> Type -> Maybe (Kind, [TypeArg], Type)
etaReduce k nAs t =
    let (topTy, tArgs) = getTypeAppl t
        (ks, newAs, ts) = etaReduceAux ([], reverse nAs, reverse tArgs)
    in case ks of
         _ : _ -> Just (typeArgsListToKind ks k,
                        reverse newAs, mkTypeAppl topTy $ reverse ts)
         [] -> Nothing

-- | add a supertype to a given type id
addSuperType :: Type -> Kind -> (Id, [TypeArg]) -> State Env ()
addSuperType t ak p@(i, nAs) = case t of
    TypeName j _ v -> if v /= 0 then
         addDiags[mkDiag Error ("illegal type variable as supertype") j]
         else addSuperId j ak i
    _ -> case etaReduce ak nAs t of
        Just (nk, rAs, rT) -> addSuperType rT nk (i, rAs)
        Nothing -> case t of
          TypeAppl (TypeName l _ _) tl | l == lazyTypeId ->
              addSuperType tl ak p
          TypeAppl t1 t2 -> if hasRedex t then addSuperType (redStep t) ak p
                            else do
            j <- newTypeIdentifier i
            let rk = rawKindOfType t1
                k = rawToKind rk
                vs = map (fst . snd) $ leaves (> 0) t1
                jTy = TypeName j rk 0
                newArgs = filter ( \ a -> getTypeVar a `elem` vs) nAs
                aTy = mkTypeAppl jTy $ map typeArgToType newArgs
            if null vs then addTypeId True NoTypeDefn rk k j else return True
            addSuperType t1 k (j, newArgs)
            tm <- gets typeMap
            addAliasType False i
                (TypeScheme nAs (expandAlias tm $ TypeAppl aTy t2) nullRange)
                $ typeArgsListToKind nAs ak
            return ()
          _ -> addSuperType (stripType "addSuperType" t) ak p

-- | generalize a type scheme for an alias type
generalizeT :: TypeScheme -> State Env TypeScheme
generalizeT sc@(TypeScheme args ty p) = do
   addDiags $ generalizable True sc
   return $ TypeScheme (genTypeArgs args) (generalize args ty) p

newTypeIdentifier :: Id -> State Env Id
newTypeIdentifier i = do
   n <- toEnvState inc
   return $ simpleIdToId $ Token ("_t" ++ show n) $ posOfId i

-- | add second identifier as super type of known first identifier
addSuperId :: Id -> Kind -> Id -> State Env ()
addSuperId j kind i = do
    tm <- gets typeMap
    cm <- gets classMap
    if i == j then return () -- silently ignore
      else if Set.member i $ supIds tm Set.empty $ Set.singleton j then
        addDiags[mkDiag Error ("subtyping cycle via '" ++ showId i "' and") j]
        else case Map.lookup i tm of
          Nothing -> return () -- previous error
          Just (TypeInfo ok ks sups defn) -> if Set.member j sups
              then addDiags[mkDiag Hint "repeated supertype" j]
              else case isLiberalKind cm ok kind of
                Just _ -> putTypeMap $ Map.insert i
                          (TypeInfo ok ks (Set.insert j sups) defn) tm
                Nothing -> let Result _ (Just rk) = anaKindM kind cm in
                           addDiags $ diffKindDiag i ok rk

-- | add an alias type definition
addAliasType :: Bool -> Id -> TypeScheme -> Kind -> State Env Bool
addAliasType b i sc fullKind = do
    newSc <- generalizeT sc
    addAliasTypeAux b i newSc fullKind

addAliasTypeAux :: Bool -> Id -> TypeScheme -> Kind -> State Env Bool
addAliasTypeAux b i (TypeScheme args ty ps) fullKind = do
    ark <- anaKind fullKind
    case args of
      t : r@( _ : _) -> do
         j <- newTypeIdentifier i
         case fullKind of
           FunKind _ _ k _ -> do
               let rk = toRaw k
               let rsc = TypeScheme r ty ps
               addAliasTypeAux False j rsc k
               tm <- gets typeMap
               addTypeId b (AliasTypeDefn $ TypeAbs t
                            (expandAlias tm $ TypeName j rk 0) ps)
                              ark fullKind i
           _ -> error "addAliasType"
      _ -> addTypeId b (AliasTypeDefn $ case args of
                        [t] -> TypeAbs t ty ps
                        _ -> ty) ark fullKind i
