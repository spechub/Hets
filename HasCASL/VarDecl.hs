{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2003
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable (MonadState)
    
analyse generic var (or type var) decls

-}

module HasCASL.VarDecl where

import HasCASL.As
import HasCASL.ClassAna
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.Id
import HasCASL.Le
import Data.Maybe
import Data.List
import Common.Lib.State
import Common.Result
import HasCASL.ClassAna
import HasCASL.TypeAna
import HasCASL.Unify
import HasCASL.Merge

-- ---------------------------------------------------------------------------
-- storing type ids with their kind and definition
-- ---------------------------------------------------------------------------

-- | store a complete type map
putTypeMap :: TypeMap -> State Env ()
putTypeMap tk =  do { e <- get; put e { typeMap = tk } }

-- | store type id and check the kind
addTypeId :: TypeDefn -> Instance -> Kind -> Id -> State Env (Maybe Id)
-- type args not yet considered for kind construction 
addTypeId defn _ kind i = 
    do nk <- expandKind kind
       if placeCount i <= kindArity TopLevel nk then
	  do addTypeKind defn i kind
	     return $ Just i 
	  else do addDiags [mkDiag Error "wrong arity of" i]
                  return Nothing

-- | store prefix type ids both with and without following places 
addTypeKind :: TypeDefn -> Id -> Kind -> State Env ()
addTypeKind d i k = 
    if isPrefix i then do addSingleTypeKind d i k
			  addSingleTypeKind d (stripFinalPlaces i) k
    else addSingleTypeKind d i k

-- | store type as is
addSingleTypeKind :: TypeDefn -> Id -> Kind -> State Env () 
addSingleTypeKind d i k = 
    do tk <- gets typeMap
       case Map.lookup i tk of
	      Nothing -> putTypeMap $ Map.insert i 
			 (TypeInfo k [] [] d) tk
	      Just (TypeInfo ok ks sups defn) -> 
		  -- check with merge
		  do checkKinds i k ok
		     if any (==k) (ok:ks)
			then addDiags [mkDiag Warning 
				 "redeclared type" i]
				 else putTypeMap $ Map.insert i 
					 (TypeInfo ok
					       (k:ks) sups defn) tk

-- | analyse a type argument
anaTypeVarDecl :: TypeArg -> State Env (Maybe TypeArg)
anaTypeVarDecl(TypeArg t k s ps) = 
    do nk <- anaKind k
       addTypeVarDecl $ TypeArg t nk s ps

-- | add an analysed type argument
addTypeVarDecl :: TypeArg -> State Env (Maybe TypeArg)
addTypeVarDecl ta@(TypeArg t k _ _) = 
    do mi <- addTypeId TypeVarDefn Plain k t
       return $ fmap (const ta) mi

-- | compute arity from a 'Kind'
kindArity :: ApplMode -> Kind -> Int
kindArity m (KindAppl k1 k2 _) =
    case m of 
	       TopLevel -> kindArity OnlyArg k1 + 
			   kindArity TopLevel k2
	       OnlyArg -> 1
kindArity m (ExtClass _ _ _) = case m of
			     TopLevel -> 0
			     OnlyArg -> 1

-- ---------------------------------------------------------------------------
-- for storing selectors and constructors
-- ---------------------------------------------------------------------------

-- | store assumptions
putAssumps :: Assumps -> State Env ()
putAssumps as =  do { e <- get; put e { assumps = as } }

-- | find information for qualified operation
partitionOpId :: Assumps -> TypeMap -> Int -> UninstOpId -> TypeScheme
	 -> ([OpInfo], [OpInfo])
partitionOpId as tm c i sc = 
    let l = Map.findWithDefault (OpInfos []) i as 
	in partition (isUnifiable tm c sc . opType) $ opInfos l

-- | storing an operation
addOpId :: UninstOpId -> TypeScheme -> [OpAttr] -> OpDefn 
	-> State Env (Maybe UninstOpId)
addOpId i (TypeScheme vs (ps :=> newTy) qs) attrs defn = 
    do as <- gets assumps
       tm <- gets typeMap
       c <- gets counter
       let sc = TypeScheme vs (ps :=> newTy) qs
           (l,r) = partitionOpId as tm c i sc
	   oInfo = OpInfo sc attrs defn 
       if null l then do putAssumps $ Map.insert i 
					(OpInfos (oInfo : r )) as
			 return $ Just i
	  else do let Result ds mo = merge (head l) oInfo
		  addDiags $ map (improveDiag i) ds
		  case mo of 
		      Nothing -> return Nothing
		      Just oi -> do putAssumps $ Map.insert i 
						   (OpInfos (oi : r )) as
				    return $ Just i

----------------------------------------------------------------------------
-- GenVarDecl
-----------------------------------------------------------------------------

addGenVarDecl :: GenVarDecl -> State Env (Maybe GenVarDecl)
addGenVarDecl(GenVarDecl v) = do mv <- addVarDecl v
				 return $ fmap GenVarDecl mv
addGenVarDecl(GenTypeVarDecl t) = do mt <- addTypeVarDecl t 
				     return $ fmap GenTypeVarDecl mt

anaGenVarDecl :: GenVarDecl -> State Env (Maybe GenVarDecl)
anaGenVarDecl(GenVarDecl v) = optAnaVarDecl v
anaGenVarDecl(GenTypeVarDecl t) = 
    anaTypeVarDecl t >>= (return . fmap GenTypeVarDecl)

convertTypeToClass :: Type -> State Env (Maybe Class)
convertTypeToClass (TypeToken t) = 
       if tokStr t == "Type" then return $ Just universe else do
          let ci = simpleIdToId t
	  e <- get					       
	  mk <- anaClassId ci
	  case mk of 
		  Nothing -> do put e
				return Nothing
		  _ -> return $ Just $ Intersection  (Set.single ci) []
convertTypeToClass (BracketType Parens ts ps) = 
       do cs <- mapM convertTypeToClass ts
	  if all isJust cs then 
	     return $ Just $ Intersection (Set.unions $ map iclass $ 
				    catMaybes cs) ps
	     else return Nothing

convertTypeToClass t = 
    do return Nothing

convertTypeToKind :: Type -> State Env (Maybe Kind)
convertTypeToKind (FunType t1 FunArr t2 ps) = 
    do mk1 <- convertTypeToKind t1
       mk2 <- convertTypeToKind t2
       case (mk1, mk2) of
           (Just k1, Just k2) -> return $ Just $ KindAppl k1 k2 ps
	   _ -> return Nothing

convertTypeToKind (BracketType Parens [t] _) = 
    do convertTypeToKind t

convertTypeToKind ty@(MixfixType [t1, TypeToken t]) = 
    let s = tokStr t 
	v = case s of 
		   "+" -> CoVar 
		   "-" -> ContraVar 
		   _ -> InVar
    in case v of 
	      InVar -> do return Nothing
	      _ -> do mk1 <- convertTypeToClass t1
		      case mk1 of 
			  Just k1 -> return $ Just $ ExtClass k1 v [tokPos t]
			  _ -> return Nothing
convertTypeToKind t = 
    do mc <- convertTypeToClass t
       return $ fmap ( \ c -> ExtClass c InVar []) mc

optAnaVarDecl :: VarDecl -> State Env (Maybe GenVarDecl)
optAnaVarDecl vd@(VarDecl v t s q) = 
    let varDecl = anaVarDecl vd >>= (return . fmap GenVarDecl) in
    if isSimpleId v then
    do mk <- convertTypeToKind t
       case mk of 
	   Just k -> do addDiags [mkDiag Hint "is type variable" v]
			tv <- anaTypeVarDecl $ TypeArg v k s q
			return $ fmap GenTypeVarDecl tv 
           _ -> varDecl
    else varDecl

-- | analyse 
anaVarDecl :: VarDecl -> State Env (Maybe VarDecl)
anaVarDecl(VarDecl v oldT sk ps) = 
    do mt <- anaStarType oldT
       case mt of 
	       Nothing -> return Nothing
	       Just t -> let s = Map.fromList $ 
				 map ( \ a@(TypeArg i k _ _) -> 
				       (a, TypeName i k 0)) $ varsOf t
	                 -- make type monomorph
	                 in  addVarDecl (VarDecl v (subst s t) sk ps)

-- | add a local variable with an analysed type
addVarDecl :: VarDecl -> State Env (Maybe VarDecl) 
addVarDecl vd@(VarDecl v t _ _) = 
    do newV <- addOpId v (simpleTypeScheme t) [] VarDefn
       return $ fmap (const vd) newV

-- | check uniqueness of variables 
checkUniqueVars :: [VarDecl] -> State Env ()
checkUniqueVars = addDiags . checkUniqueness . map ( \ (VarDecl v _ _ _) -> v )

-- | filter out assumption
filterAssumps  :: (OpInfo -> Bool) -> Assumps -> Assumps
filterAssumps p =
    Map.filter (not . null . opInfos) .
       Map.map (OpInfos . filter p . opInfos)

