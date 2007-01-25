{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable

conversion from As to Le
-}

module HasCASL.AsToLe where

import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Id
import Common.Result
import Common.Prec
import Common.Lib.State
import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set

import HasCASL.As
import HasCASL.Le
import HasCASL.TypeAna
import HasCASL.ClassAna
import HasCASL.VarDecl
import HasCASL.Unify
import HasCASL.OpDecl
import HasCASL.TypeDecl
import HasCASL.Builtin
import HasCASL.MapTerm
import Data.Maybe

-- * extract predicate ids from As for mixfix analysis

type Ids = Set.Set Id

unite :: [Ids] -> Ids
unite = Set.unions

idsOfBasicSpec :: BasicSpec -> Ids
idsOfBasicSpec (BasicSpec l) = unite $ map (idsOfBasicItem . item) l

idsOfBasicItem :: BasicItem -> Ids
idsOfBasicItem (SigItems i) = idsOfSigItems i
idsOfBasicItem (ClassItems _ l _ ) = unite $ map (idsOfClassItem . item) l
idsOfBasicItem (GenItems l _) = unite $ map (idsOfSigItems . item) l
idsOfBasicItem (Internal l _) = unite $ map (idsOfBasicItem . item) l
idsOfBasicItem _ = Set.empty

idsOfClassItem :: ClassItem -> Ids
idsOfClassItem (ClassItem _ l _) = unite $ map (idsOfBasicItem . item) l

idsOfSigItems :: SigItems -> Ids
idsOfSigItems (TypeItems _ _ _) = Set.empty
idsOfSigItems (OpItems b l _) = unite $ map (idsOfOpItem b . item) l

idsOfOpItem :: OpBrand -> OpItem -> Ids
idsOfOpItem b (OpDecl os _ _ _) =
    let ois = Set.fromList $ map ( \ (OpId i _ _) -> i) os
        in case b of
                  Pred -> ois
                  _ -> Set.empty
idsOfOpItem b (OpDefn (OpId i _ _) _ _ _ _ _) =
        case b of
                  Pred -> (Set.singleton i)
                  _ -> Set.empty

-- * basic analysis

-- | basic analysis
basicAnalysis :: (BasicSpec, Env, GlobalAnnos) ->
                 Result (BasicSpec, Env, [Named Sentence])
basicAnalysis (b, e, ga) =
    let (nb, ne) = runState (anaBasicSpec ga b) e
        in Result (reverse $ envDiags ne) $
           Just (nb, cleanEnv ne, reverse $ sentences ne)

-- | is the signature empty?
isEmptyEnv :: Env -> Bool
isEmptyEnv e = Map.null (classMap e)
               && Map.null (typeMap e)
               && Map.null (assumps e)

-- | is the first argument a subsignature of the second?
isSubEnv :: Env -> Env -> Bool
isSubEnv e1 e2 = isEmptyEnv $ diffEnv e1 e2

-- a rough equality
instance Eq Env where
    e1 == e2 = isSubEnv e1 e2 && isSubEnv e2 e1

-- | compute difference of signatures
diffEnv :: Env -> Env -> Env
diffEnv e1 e2 = let tm = typeMap e2 in
    initialEnv
       { classMap = Map.differenceWith diffClass (classMap e1) (classMap e2)
       , typeMap = Map.differenceWith diffType (typeMap e1) tm
       , assumps = Map.differenceWith (diffAss $ addUnit tm)
                   (assumps e1) (assumps e2)
       }

-- | compute difference of class infos
diffClass :: ClassInfo -> ClassInfo -> Maybe ClassInfo
diffClass _ _ = Nothing

-- | compute difference of type infos
diffType :: TypeInfo -> TypeInfo -> Maybe TypeInfo
diffType _ _ = Nothing

-- | compute difference of overloaded operations
diffAss :: TypeMap -> OpInfos -> OpInfos -> Maybe OpInfos
diffAss tm (OpInfos l1) (OpInfos l2) =
    let l3 = diffOps l1 l2 in
        if null l3 then Nothing else Just (OpInfos l3)
    where diffOps [] _ = []
          diffOps (o:os) ps =
              let rs = diffOps os ps
                  n = mapOpInfo (id, expandAlias tm) o
              in if any (instScheme tm 1 (opType n) . expand tm . opType) ps
                 then rs else n:rs

-- | environment with predefined types and operations
addPreDefs :: Env -> Env
addPreDefs e = e { typeMap = addUnit $ typeMap e
                    , assumps = addOps $ assumps e }

-- | environment with predefined types and operations
preEnv :: Env
preEnv = addPreDefs initialEnv

-- | clean up finally accumulated environment
cleanEnv :: Env -> Env
cleanEnv e = diffEnv initialEnv
             { classMap = classMap e
             , typeMap = typeMap e
             , assumps = assumps e }
             preEnv where

-- | analyse basic spec
anaBasicSpec :: GlobalAnnos -> BasicSpec -> State Env BasicSpec
anaBasicSpec ga b@(BasicSpec l) = do
    e <- get
    let newAs = assumps e
        preds = Rel.keysSet $ Map.filter (any ( \ oi ->
                                 case opDefn oi of
                                 NoOpDefn Pred -> True
                                 Definition Pred _ -> True
                                 _ -> False) . opInfos) newAs
        newPreds = idsOfBasicSpec b
        rels = Set.union preds newPreds
        newGa = addBuiltins ga
        precs = mkPrecIntMap $ prec_annos newGa
    put (addPreDefs e) { preIds = (precs, rels), globAnnos = newGa }
    ul <- mapAnM (anaBasicItem newGa) l
    return $ BasicSpec ul

-- | analyse basic item
anaBasicItem :: GlobalAnnos -> BasicItem -> State Env BasicItem
anaBasicItem ga (SigItems i) = fmap SigItems $ anaSigItems ga Loose i
anaBasicItem ga (ClassItems inst l ps) =
    do ul <- mapAnM (anaClassItem ga inst) l
       return $ ClassItems inst ul ps
anaBasicItem _ (GenVarItems l ps) =
    do ul <- mapM (anaddGenVarDecl True) l
       return $ GenVarItems (catMaybes ul) ps
anaBasicItem ga (ProgItems l ps) =
    do ul <- mapAnMaybe (anaProgEq ga) l
       return $ ProgItems ul ps
anaBasicItem _ (FreeDatatype l ps) =
    do al <- mapAnMaybe ana1Datatype l
       tys <- mapM (dataPatToType . item) al
       mapAnMaybe (anaDatatype Free Plain tys) al
       addDataSen tys
       return $ FreeDatatype l ps
anaBasicItem ga (GenItems l ps) =
    do ul <- mapAnM (anaSigItems ga Generated) l
       return $ GenItems ul ps
anaBasicItem ga (AxiomItems decls fs ps) =
    do tm <- gets typeMap -- save type map
       as <- gets assumps -- save vars
       ds <- mapM (anaddGenVarDecl True) decls
       ts <- mapM (anaFormula ga) fs
       putTypeMap tm -- restore
       putAssumps as -- restore
       let newFs = catMaybes ts
           newDs = catMaybes ds
           sens = map ( \ f -> (emptyName $ Formula $ mkForall newDs
                            (item f) ps) { senName = getRLabel f })
                  newFs
       appendSentences sens
       return $ AxiomItems newDs newFs ps
anaBasicItem ga (Internal l ps) =
    do ul <- mapAnM (anaBasicItem ga) l
       return $ Internal ul ps

-- | quantify
mkForall :: [GenVarDecl] -> Term -> Range -> Term
mkForall _vs t _ps = t -- look for a minimal quantification
  -- if null vs then t else QuantifiedTerm Universal vs t ps

-- | analyse sig items
anaSigItems :: GlobalAnnos -> GenKind -> SigItems -> State Env SigItems
anaSigItems ga gk (TypeItems inst l ps) =
    do ul <- anaTypeItems ga gk inst l
       return $ TypeItems inst ul ps
anaSigItems ga _ (OpItems b l ps) =
    do ul <- mapAnMaybe (anaOpItem ga b) l
       return $ OpItems b ul ps

-- | analyse a class item
anaClassItem :: GlobalAnnos -> Instance -> ClassItem
                    -> State Env ClassItem
anaClassItem ga _ (ClassItem d l ps) =
    do cd <- anaClassDecls d
       ul <- mapAnM (anaBasicItem ga) l
       return $ ClassItem cd ul ps
