{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable 

   conversion from As to Le
-}

module HasCASL.AsToLe where

import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Result
import Common.Lib.State
import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set

import HasCASL.As
import HasCASL.AsToIds
import HasCASL.Le
import HasCASL.ClassDecl
import HasCASL.VarDecl
import HasCASL.Unify
import HasCASL.OpDecl
import HasCASL.TypeDecl
import HasCASL.Builtin
import HasCASL.MapTerm
import Data.Maybe

-- | basic analysis
basicAnalysis :: (BasicSpec, Env, GlobalAnnos) -> 
                 Result (BasicSpec, Env, Env, [Named Sentence])
basicAnalysis (b, e, ga) = 
    let (nb, ne) = runState (anaBasicSpec ga b) e 
        ce = cleanEnv ne
        in Result (reverse $ envDiags ne) $ 
           Just (nb, diffEnv ce e, ce, reverse $ sentences ne) 

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
       , assumps = Map.differenceWith (diffAss tm) (assumps e1) (assumps e2)
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
             , typeMap = Map.filter (not . isTypeVarDefn) $ typeMap e
             , assumps = filterVars $ assumps e }
             preEnv where
             filterVars :: Assumps -> Assumps
             filterVars = filterAssumps (not . isVarDefn)

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
    put (addPreDefs e) { preIds = (precs, rels) }
    ul <- mapAnM (anaBasicItem newGa) l
    return $ BasicSpec ul

-- | analyse basic item
anaBasicItem :: GlobalAnnos -> BasicItem -> State Env BasicItem
anaBasicItem ga (SigItems i) = fmap SigItems $ anaSigItems ga Loose i
anaBasicItem ga (ClassItems inst l ps) = 
    do ul <- mapAnM (anaClassItem ga inst) l
       return $ ClassItems inst ul ps
anaBasicItem _ (GenVarItems l ps) = 
    do ul <- mapM anaGenVarDecl l
       return $ GenVarItems (catMaybes ul) ps
anaBasicItem ga (ProgItems l ps) = 
    do ul <- mapAnMaybe (anaProgEq ga) l
       return $ ProgItems ul ps
anaBasicItem _ (FreeDatatype l ps) = 
    do al <- mapAnMaybe ana1Datatype l
       let tys = map (dataPatToType . item) al
       ul <- mapAnMaybe (anaDatatype Free Plain tys) al
       addDataSen tys
       return $ FreeDatatype ul ps
anaBasicItem ga (GenItems l ps) = 
    do ul <- mapAnM (anaSigItems ga Generated) l
       return $ GenItems ul ps
anaBasicItem ga (AxiomItems decls fs ps) = 
    do tm <- gets typeMap -- save type map
       as <- gets assumps -- save vars
       ds <- mapM anaGenVarDecl decls
       ts <- mapM (anaFormula ga) fs
       putTypeMap tm -- restore 
       putAssumps as -- restore
       let newFs = catMaybes ts
           sens = map ( \ f -> NamedSen (getRLabel f) True $ Formula $ item f) 
                  newFs 
       appendSentences sens
       return $ AxiomItems (catMaybes ds) newFs ps
anaBasicItem ga (Internal l ps) = 
    do ul <- mapAnM (anaBasicItem ga) l
       return $ Internal ul ps

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
