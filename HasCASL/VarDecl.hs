{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

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

-- | add diagnostic messages 
addDiags :: [Diagnosis] -> State Env ()
addDiags ds =
    do e <- get
       put $ e {envDiags = ds ++ envDiags e}

anaStarType :: Type -> State Env (Maybe Type)
anaStarType t = do mp <- fromResult (anaType (Just star, t) . typeMap)
		   return $ fmap snd mp

anaKind :: Kind -> State Env Kind
anaKind k = toState star $ anaKindM k

toState :: a -> (Env -> Result a) -> State Env a
toState bot r = do
     ma <- fromResult r
     case ma of 
	  Nothing -> return bot  
          Just a -> return a

fromResult :: (Env -> Result a) -> State Env (Maybe a)
fromResult f = do 
   e <- get
   let r = f e
   addDiags $ diags r
   return $ maybeResult r

-- ---------------------------------------------------------------------------
-- storing type ids with their kind and definition
-- ---------------------------------------------------------------------------

-- | store a complete type map
putTypeMap :: TypeMap -> State Env ()
putTypeMap tk =  do { e <- get; put e { typeMap = tk } }

-- | store type id and check kind arity (warn on redeclared types)
addTypeId :: Bool -> TypeDefn -> Instance -> Kind -> Id -> State Env (Maybe Id)
addTypeId warn defn _ kind i = 
    do let nk = rawKind kind
       if placeCount i <= kindArity TopLevel nk then
	  do addTypeKind warn defn i kind
	     return $ Just i 
	  else do addDiags [mkDiag Error "wrong arity of" i]
                  return Nothing

-- | store type as is (warn on redeclared types)
addTypeKind :: Bool -> TypeDefn -> Id -> Kind -> State Env () 
addTypeKind warn d i k = 
    do tk <- gets typeMap
       c <- gets counter
       let rk = rawKind k
       case Map.lookup i tk of
	      Nothing -> putTypeMap $ Map.insert i 
			 (TypeInfo rk [k] [] d) tk
	      Just (TypeInfo ok ks sups defn) -> 
		  if rk == ok
		     then do let isKnownInst = k `elem` ks
				 insts = if isKnownInst then ks else
					mkIntersection (k:ks)
				 Result ds mDef = mergeTypeDefn tk c defn d
			     if warn && isKnownInst && case (defn, d) of 
			         (PreDatatype, DatatypeDefn _ _ _) -> False
			         _ -> True
				then
			        addDiags [mkDiag Hint 
					  "redeclared type" i]
				else return ()
		             case mDef of
			         Just newDefn -> putTypeMap $ Map.insert i 
					 (TypeInfo ok insts sups newDefn) tk
				 Nothing -> addDiags $ map (improveDiag i) ds
		     else addDiags $ diffKindDiag i ok rk 

-- | analyse a type argument and look up a missing kind
anaTypeVarDecl :: TypeArg -> State Env (Maybe TypeArg)
anaTypeVarDecl(TypeArg t k s ps) = 
    case k of 
    MissingKind -> do 
       tk <- gets typeMap
       let rm = getIdKind tk t
       case maybeResult rm of 
 	      Nothing -> anaTypeVarDecl(TypeArg t star s ps)
	      Just oldK -> addTypeVarDecl False (TypeArg t oldK s ps)
    _ -> do nk <- anaKind k
	    addTypeVarDecl True $ TypeArg t nk s ps

-- | add an analysed type argument (warn on redeclared types)
addTypeVarDecl :: Bool -> TypeArg -> State Env (Maybe TypeArg)
addTypeVarDecl warn ta@(TypeArg t k _ _) = 
    do mi <- addTypeId warn TypeVarDefn Plain k t
       return $ fmap (const ta) mi

-- | compute arity from a 'Kind'
kindArity :: ApplMode -> Kind -> Int
kindArity m k = 
    case k of 
    FunKind k1 k2 _ -> case m of 
		       TopLevel -> kindArity OnlyArg k1 + 
				   kindArity TopLevel k2
		       OnlyArg -> 1
    Universe _ -> case m of
		  TopLevel -> 0
		  OnlyArg -> 1
    ClassKind _ ck -> kindArity m ck
    Downset _ _ dk _ -> kindArity m dk
    Intersection (k1:_) _ -> kindArity m k1
    ExtKind ek _ _ -> kindArity m ek
    _ -> error "kindArity"


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
addOpId i sc attrs defn = 
    do as <- gets assumps
       tm <- gets typeMap
       c <- gets counter
       let (TypeScheme _ (_ :=> ty) _) = sc 
           ds = if placeCount i > 1 then case unalias tm ty of 
		   FunType (ProductType ts _) _ _ _ ->
		     if placeCount i /= length ts then 
			    [mkDiag Error "wrong number of places in" i]
                     else []
		   _ -> [mkDiag Error "expected tuple argument for" i]
		 else []
           (l,r) = partitionOpId as tm c i sc
	   oInfo = OpInfo sc attrs defn 
       if null ds then 
          if null l then do putAssumps $ Map.insert i 
					(OpInfos (oInfo : r )) as
			    return $ Just i
	  else do let Result es mo = mergeOpInfo tm c (head l) oInfo
		  addDiags $ map (improveDiag i) es
		  case mo of 
		      Nothing -> return Nothing
		      Just oi -> do putAssumps $ Map.insert i 
						   (OpInfos (oi : r )) as
				    return $ Just i
	  else do addDiags ds
		  return Nothing

----------------------------------------------------------------------------
-- GenVarDecl
-----------------------------------------------------------------------------

addGenVarDecl :: GenVarDecl -> State Env (Maybe GenVarDecl)
addGenVarDecl(GenVarDecl v) = do mv <- addVarDecl v
				 return $ fmap GenVarDecl mv
addGenVarDecl(GenTypeVarDecl t) = do mt <- addTypeVarDecl True t 
				     return $ fmap GenTypeVarDecl mt

anaGenVarDecl :: GenVarDecl -> State Env (Maybe GenVarDecl)
anaGenVarDecl(GenVarDecl v) = optAnaVarDecl v
anaGenVarDecl(GenTypeVarDecl t) = 
    anaTypeVarDecl t >>= (return . fmap GenTypeVarDecl)

convertTypeToKind :: Type -> State Env (Maybe Kind)
convertTypeToKind (FunType t1 FunArr t2 ps) = 
    do mk1 <- convertTypeToKind t1
       mk2 <- convertTypeToKind t2
       case (mk1, mk2) of
           (Just k1, Just k2) -> case k2 of 
	       ExtKind _ _ _ -> return Nothing
	       _ -> return $ Just $ FunKind k1 k2 ps
	   _ -> return Nothing

convertTypeToKind (BracketType Parens [] _) = 
    return Nothing
convertTypeToKind (BracketType Parens [t] _) = 
    convertTypeToKind t
convertTypeToKind (BracketType Parens ts ps) = 
       do cs <- mapM convertTypeToKind ts
	  if all isJust cs then 
	     do let k:ks = catMaybes cs 
		    rk = rawKind k
		if all ((==rk) . rawKind) ks then
		   return $ Just $ Intersection (k:ks) ps
		   else return Nothing
	     else return Nothing
convertTypeToKind (MixfixType [t1, TypeToken t]) = 
    let s = tokStr t 
	v = case s of 
		   "+" -> CoVar 
		   "-" -> ContraVar 
		   _ -> InVar
    in case v of 
	      InVar -> do return Nothing
	      _ -> do mk1 <- convertTypeToKind t1
		      case mk1 of 
			  Just k1 -> return $ Just $ ExtKind k1 v [tokPos t]
			  _ -> return Nothing
convertTypeToKind(TypeToken t) = 
       if tokStr t == "Type" then return $ Just $ Universe [tokPos t] else do
          let ci = simpleIdToId t
	  cm <- gets classMap					       
	  let rm = anaClassId ci cm
	  case maybeResult rm of 
		  Nothing -> return Nothing
		  Just k -> return $ Just $ ClassKind ci k
convertTypeToKind _ = 
    do return Nothing

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
	       Just t -> let s = Map.fromAscList $ 
				 map ( \ a@(TypeArg i k _ _) -> 
				       (a, TypeName i k 0)) $ 
				 Set.toList $ varsOf t
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

-- | check uniqueness of type variables 
checkUniqueTypevars :: [TypeArg] -> State Env ()
checkUniqueTypevars = addDiags . checkUniqueness 
		      . map ( \ (TypeArg v _ _ _) -> v )

-- | filter out assumption
filterAssumps  :: (OpInfo -> Bool) -> Assumps -> Assumps
filterAssumps p =
    Map.filter (not . null . opInfos) .
       Map.map (OpInfos . filter p . opInfos)

