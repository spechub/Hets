{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 

   conversion from As to Le
-}

module HasCASL.AsToLe where

import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Lib.State
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.Result
import Common.Id
import HasCASL.As
import HasCASL.AsToIds
import HasCASL.Le
import HasCASL.ClassDecl
import HasCASL.VarDecl
import HasCASL.Unify
import HasCASL.OpDecl
import HasCASL.TypeDecl
import HasCASL.TypeCheck
import HasCASL.MixAna
import Data.Maybe
import Data.List

-- | basic analysis
basicAnalysis :: (BasicSpec, Env, GlobalAnnos) -> 
                 Result (BasicSpec, Env, Env, [Named Term])
basicAnalysis (b, e, ga) = 
    let (nb, ne) = runState (anaBasicSpec ga b) e 
	ce = cleanEnv ne
        in Result (reverse $ envDiags ne) $ 
           Just (nb, diffEnv ce e, ce, reverse $ sentences ne) 

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

-- | Check if two OpTypes are equal except from totality or partiality
compatibleOpTypes :: TypeScheme -> TypeScheme -> Bool
compatibleOpTypes = isUnifiable Map.empty 0

-- | compute difference of overloaded operations
diffAss :: TypeMap -> OpInfos -> OpInfos -> Maybe OpInfos
diffAss tm (OpInfos l1) (OpInfos l2) = 
    let l3 = diffOps l1 l2 in
	if null l3 then Nothing else Just (OpInfos l3)
    where diffOps [] _ = []
	  diffOps (o:os) ps = 
	      let rs = diffOps os ps in
	      if any (\ p -> isUnifiable tm 0 (opType o) (opType p)) ps
		 then rs else o:rs
 
-- | clean up finally accumulated environment
cleanEnv :: Env -> Env
cleanEnv e = diffEnv initialEnv 
	     { classMap = classMap e
             , typeMap = Map.filter (not . isTypeVarDefn) (typeMap e)
	     , assumps = filterAssumps (not . isVarDefn) (assumps e) }
	     preEnv 

-- | environment with predefined types and operations
preEnv :: Env  
preEnv = initialEnv { typeMap = addUnit Map.empty
		    , assumps = addOps Map.empty }

addPreIds :: (PrecMap, Set.Set Id) -> State Env ()
addPreIds r = do e <- get
		 put e { preIds = r }

-- | analyse basic spec
anaBasicSpec :: GlobalAnnos -> BasicSpec -> State Env BasicSpec
anaBasicSpec ga b@(BasicSpec l) = do 
    tm <- gets typeMap
    as <- gets assumps
    putTypeMap $ addUnit tm
    putAssumps $ addOps as
    newAs <- gets assumps
    let preds = Set.fromDistinctAscList 
		   $ Map.keys $ Map.filter (any ( \ oi -> 
				 case opDefn oi of
				 NoOpDefn Pred -> True
				 Definition Pred _ -> True
				 _ -> False) . opInfos) newAs
	newPreds = idsOfBasicSpec b 
	rels = Set.union preds newPreds
	newGa = addBuiltins ga
	precs = mkPrecIntMap $ prec_annos newGa
    addPreIds (precs, rels)
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
    do ul <- mapAnM (anaProgEq ga) l
       return $ ProgItems ul ps
anaBasicItem _ (FreeDatatype l ps) = 
    do al <- mapAnMaybe ana1Datatype l
       let tys = map (dataPatToType . item) al
       ul <- mapAnM (anaDatatype Free Plain tys) al
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
           sens = map ( \ f -> NamedSen (getRLabel f) $ item f) newFs 
       appendSentences sens
       return $ AxiomItems (catMaybes ds) newFs ps
anaBasicItem ga (Internal l ps) = 
    do ul <- mapAnM (anaBasicItem ga) l
       return $ Internal ul ps

-- | add sentences
appendSentences :: [Named Term] -> State Env ()
appendSentences fs =
    do e <- get
       put $ e {sentences = sentences e ++ fs}

-- | analyse sig items
anaSigItems :: GlobalAnnos -> GenKind -> SigItems -> State Env SigItems
anaSigItems ga gk (TypeItems inst l ps) = 
    do ul <- anaTypeItems ga gk inst l
       return $ TypeItems inst ul ps
anaSigItems ga _ (OpItems b l ps) = 
    do ul <- mapAnM (anaOpItem ga b) l
       return $ OpItems b ul ps

-- | analyse a class item
anaClassItem :: GlobalAnnos -> Instance -> ClassItem 
		    -> State Env ClassItem
anaClassItem ga _ (ClassItem d l ps) = 
    do cd <- anaClassDecls d 
       ul <- mapAnM (anaBasicItem ga) l
       return $ ClassItem cd ul ps



