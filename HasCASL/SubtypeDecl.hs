{- |
Module      :  $Header$
Description :  analysis of subtype declarations
Copyright   :  (c) Christian Maeder and Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

analyse subtype decls
-}

module HasCASL.SubtypeDecl
    ( addSuperType
    , addAliasType
    ) where

import Common.Id
import Common.Lib.State
import qualified Data.Set as Set
import qualified Data.Map as Map
import Common.Result

import HasCASL.As
import HasCASL.FoldType
import HasCASL.AsUtils
import HasCASL.Le
import HasCASL.TypeAna
import HasCASL.ClassAna
import HasCASL.Unify
import HasCASL.VarDecl

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
         else addSuperId i ak j
    _ -> case etaReduce ak nAs t of
        Just (nk, rAs, rT) -> addSuperType rT nk (i, rAs)
        Nothing -> case t of
          TypeAppl (TypeName l _ _) tl | l == lazyTypeId ->
              addSuperType tl ak p
          TypeAppl t1 t2 -> case redStep t of
           Just r -> addSuperType r ak p
           Nothing -> do
            j <- newTypeIdentifier i
            let rk = rawKindOfType t1
                k = rawToKind rk
                vs = freeTVarIds t1
                newArgs = filter ( \ a -> getTypeVar a `elem` vs) nAs
                jTy = TypeName j (typeArgsListToRawKind newArgs rk) 0
                aTy = mkTypeAppl jTy $ map typeArgToType newArgs
            if null vs then addTypeId True NoTypeDefn k j else return True
            addSuperType t1 k (j, newArgs)
            tm <- gets typeMap
            addAliasType False i
                (TypeScheme nAs (expandAlias tm $ TypeAppl aTy t2) nullRange)
                $ typeArgsListToKind nAs ak
            return ()
          KindedType ty _ _ -> addSuperType ty ak p
          ExpandedType t1 t2 -> do
            addSuperType t1 ak p
            addSuperType t2 ak p
          _ -> addDiags[mkDiag Error ("unexpected type as supertype") t]

-- | generalize a type scheme for an alias type
generalizeT :: TypeScheme -> State Env TypeScheme
generalizeT sc@(TypeScheme args ty p) = do
   addDiags $ generalizable True sc
   return $ TypeScheme (genTypeArgs args) (generalize args ty) p

newTypeIdentifier :: Id -> State Env Id
newTypeIdentifier i = do
   n <- toEnvState inc
   return $ Id [genToken $ "t" ++ show n] [i] $ posOfId i

-- | add second identifier as super type of known first identifier
addSuperId :: Id -> Kind -> Id -> State Env ()
addSuperId i kind j = do
    tm <- gets typeMap
    cm <- gets classMap
    if i == j then return () -- silently ignore
      else case Map.lookup i tm of
          Nothing -> return () -- previous error
          Just (TypeInfo ok ks sups defn) -> if Set.member j sups
              then addDiags[mkDiag Hint "repeated supertype" j]
              else if Set.member i $ superIds tm j then do
                   addDiags[mkDiag Warning
                            ("made '" ++ showId i "' an alias of") j]
                   addAliasType False i (TypeScheme [] (TypeName j ok 0)
                                                    $ posOfId j) kind
                   return ()
                else let Result _ (Just rk) = anaKindM kind cm in
                maybe (addDiags $ diffKindDiag i ok rk)
                (const $ putTypeMap $ Map.insert i
                          (TypeInfo ok ks (Set.insert j sups) defn) tm)
                $ minRawKind "" ok rk

-- | add an alias type definition
addAliasType :: Bool -> Id -> TypeScheme -> Kind -> State Env Bool
addAliasType b i sc fullKind = do
    newSc <- generalizeT sc
    addAliasTypeAux b i newSc fullKind

addAliasTypeAux :: Bool -> Id -> TypeScheme -> Kind -> State Env Bool
addAliasTypeAux b i (TypeScheme args ty ps) fullKind =
  if elem i $ map (fst . snd) $ leaves (== 0) ty then do
    addDiags[mkDiag Error "cyclic alias type" i]
    return False
  else addTypeId b (AliasTypeDefn $ foldr ( \ t y -> TypeAbs t y ps) ty args)
        fullKind i
