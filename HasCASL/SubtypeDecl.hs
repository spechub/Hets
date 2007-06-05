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
    , generalizeT
    , addSuperType
    , addSuperId
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

-- lifted 'anaKindM'
anaKind :: Kind -> State Env RawKind
anaKind k = do
    mrk <- fromResult $ anaKindM k . classMap
    case mrk of
      Nothing -> error "anaKind"
      Just rk -> return rk

-- | add a supertype to a given type id
addSuperType :: Type -> Kind -> (Id, [TypeArg]) -> State Env ()
addSuperType t ak p@(i, nAs) = case t of
    TypeName j _ v -> if v /= 0 then
         addDiags[mkDiag Error ("illegal type variable as supertype") j]
         else addSuperId j i
    TypeAppl (TypeName l _ _) tl | l == lazyTypeId -> addSuperType tl ak p
    TypeAppl t1 t2 -> if hasRedex t then addSuperType (redStep t) ak p else do
        j <- newSubTypeIdentifier i
        let rk = rawKindOfType t1
            k = rawToKind rk
            vs = map (fst . snd) $ leaves (> 0) t1
            jTy = TypeName j rk 0
            newArgs = filter ( \ a -> getTypeVar a `elem` vs) nAs
            aTy = mkTypeAppl jTy $ map typeArgToType newArgs
        if null vs then addTypeId True NoTypeDefn Plain rk k j else return True
        addSuperType t1 k (j, newArgs)
        tm <- gets typeMap
        let newTy = expandAlias tm $ TypeAppl aTy t2
        newSc@(TypeScheme rArgs _ _) <- generalizeT $
                        TypeScheme nAs newTy nullRange
        let fullKind = typeArgsListToKind rArgs ak
        ark <- anaKind fullKind
        addTypeId False (AliasTypeDefn newSc) Plain ark fullKind i
        return ()
    _ -> addSuperType (stripType "addSuperType" t) ak p

-- | generalize a type scheme for an alias type
generalizeT :: TypeScheme -> State Env TypeScheme
generalizeT sc@(TypeScheme args ty p) = do
   addDiags $ generalizable True sc
   return $ TypeScheme args (generalize args ty) p

newSubTypeIdentifier :: Id -> State Env Id
newSubTypeIdentifier i = do
   n <- toEnvState inc
   return $ simpleIdToId $ Token ("_t" ++ show n) $ posOfId i

-- | add second identifier as super type of known first identifier
addSuperId :: Id -> Id -> State Env ()
addSuperId j i = do
    tm <- gets typeMap
    if i == j then return () -- silently ignore
      else if Set.member i $ supIds tm Set.empty $ Set.singleton j then
        addDiags[mkDiag Error ("subtyping cycle via '" ++ showId i "' and") j]
        else case Map.lookup i tm of
          Nothing -> return () -- previous error
          Just (TypeInfo ok ks sups defn) -> if Set.member j sups
              then addDiags[mkDiag Hint "repeated supertype" j]
              else putTypeMap $ Map.insert i
                       (TypeInfo ok ks (Set.insert j sups) defn) tm
