{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  non-portable (MonadState)
    
analyse generic var (or type var) decls

-}

module HasCASL.VarDecl where

import Data.Maybe
import Data.List as List
import Control.Monad

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.Id
import Common.AS_Annotation
import Common.Lib.State
import Common.Result

import HasCASL.As
import HasCASL.AsUtils
import HasCASL.Le
import HasCASL.ClassAna
import HasCASL.TypeAna
import HasCASL.Unify
import HasCASL.Merge
import HasCASL.Builtin

-- | add diagnostic messages 
addDiags :: [Diagnosis] -> State Env ()
addDiags ds =
    do e <- get
       put $ e {envDiags = ds ++ envDiags e}

-- | add sentences
appendSentences :: [Named Sentence] -> State Env ()
appendSentences fs =
    do e <- get
       put $ e {sentences = sentences e ++ fs}

anaStarType :: Type -> State Env (Maybe Type)
anaStarType t = do mp <- fromResult (anaType (Just star, t) . typeMap)
		   return $ fmap snd mp

anaInstTypes :: [Type] -> State Env [Type]
anaInstTypes ts = if null ts then return []
   else do mp <- fromResult (anaType (Nothing, head ts) . typeMap)
	   rs <- anaInstTypes $ tail ts
	   return $ case mp of
		   Nothing -> rs
		   Just (_, ty) -> ty:rs

anaTypeScheme :: TypeScheme -> State Env (Maybe TypeScheme)
anaTypeScheme (TypeScheme tArgs (q :=> ty) p) =
    do tm <- gets typeMap    -- save global variables  
       mArgs <- mapM anaTypeVarDecl tArgs
       let newArgs = catMaybes mArgs  
       checkUniqueTypevars newArgs
       mt <- anaStarType ty
       putTypeMap tm       -- forget local variables 
       case mt of 
           Nothing -> return Nothing
	   Just newTy -> generalize $ TypeScheme newArgs (q :=> newTy) p

generalize :: TypeScheme -> State Env (Maybe TypeScheme)
generalize (TypeScheme newArgs (q :=> newTy) p) = do
 	       let fvs = varsOf newTy
		   ts = zipWith ( \ (TypeArg i k _ _) n -> 
				  TypeName i k n) fvs [-1, -2..]
		   m = Map.fromList $ zip fvs ts
		   qTy = q :=> repl m newTy
		   restVars = fvs List.\\ newArgs
	       if null restVars then
	          return $ Just $ TypeScheme newArgs qTy p
	          else if null newArgs then 
		       return $ Just $ TypeScheme fvs qTy p
		  else do addDiags [mkDiag Error 
				    ("unbound type variable(s)\n\t"
				     ++ showSepList ("," ++) showPretty 
				     restVars " in") newTy]
                          return Nothing

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
	      Nothing -> case d of
	          TypeVarDefn _ -> do 
		      (_, v) <- toEnvState $ freshVar (posOfId i) 
		      putTypeMap $ Map.insert i 
			 (TypeInfo rk [k] [] $ TypeVarDefn v) tk
		  _ -> putTypeMap $ Map.insert i (TypeInfo rk [k] [] d) tk
	      Just (TypeInfo ok ks sups defn) -> 
		  if rk == ok
		     then do let isKnownInst = k `elem` ks
				 insts = if isKnownInst then ks else
					Set.toList $ mkIntersection (k:ks)
				 Result ds mDef = mergeTypeDefn tk c defn d
			     if warn && isKnownInst && case (defn, d) of 
			         (PreDatatype, DatatypeDefn _) -> False
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
    do mi <- addTypeId warn (TypeVarDefn 0) Plain k t
       return $ fmap (const ta) mi

-- | compute arity from a 'Kind'
kindArity :: ApplMode -> Kind -> Int
kindArity m k = 
    case k of 
    FunKind k1 k2 _ -> case m of 
		       TopLevel -> kindArity OnlyArg k1 + 
				   kindArity TopLevel k2
		       OnlyArg -> 1
    Intersection [] _ -> case m of
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

-- | get matching information of uninstantiated identifier
findOpId :: Env -> UninstOpId -> TypeScheme -> Maybe OpInfo
findOpId e i sc = listToMaybe $ fst $ partitionOpId e i sc

-- | partition information of an uninstantiated identifier
partitionOpId :: Env -> UninstOpId -> TypeScheme -> ([OpInfo], [OpInfo])
partitionOpId e i sc = 
    let l = Map.findWithDefault (OpInfos []) i $ assumps e
    in partition (isUnifiable (typeMap e) (counter e) sc . opType) $ opInfos l

-- | storing an operation
addOpId :: UninstOpId -> TypeScheme -> [OpAttr] -> OpDefn 
	-> State Env (Maybe UninstOpId)
addOpId i sc attrs defn = 
    do e <- get
       let tm = typeMap e
	   as = assumps e
	   c = counter e
           (TypeScheme _ (_ :=> ty) _) = sc 
           ds = if placeCount i > 1 then case unalias ty of 
		   FunType arg _ _ _ -> case unalias arg of
		       ProductType ts _ -> if placeCount i /= length ts then 
			    [mkDiag Error "wrong number of places in" i]
		            else [] 
		       _ -> [mkDiag Error "expected tuple argument for" i]
		   _ -> [mkDiag Error "expected function type for" i]
		 else []
           (l,r) = partitionOpId e i sc
	   oInfo = OpInfo sc attrs defn 
       if null ds then 
	       do let Result es mo = foldM (mergeOpInfo tm c) oInfo l
		  addDiags $ map (improveDiag i) es
	          if i `elem` map fst bList then addDiags $ [mkDiag Error 
			  "illegal overloading of predefined identifier" i]
		      else return ()
		  case mo of 
		      Nothing -> return Nothing
		      Just oi -> do putAssumps $ Map.insert i 
						   (OpInfos (oi : r)) as
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
	mv = case s of 
		   "+" -> Just CoVar 
		   "-" -> Just ContraVar 
		   _ -> Nothing
    in case mv of 
	      Nothing -> do return Nothing
	      Just v -> do 
		  mk1 <- convertTypeToKind t1
		  case mk1 of 
			  Just k1 -> return $ Just $ ExtKind k1 v [tokPos t]
			  _ -> return Nothing
convertTypeToKind(TypeToken t) = 
       if tokStr t == "Type" then return $ Just $ Intersection [] [tokPos t] 
	  else do
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
    let varDecl = do mvd <- anaVarDecl vd
		     case mvd of 
		         Nothing -> return Nothing
			 Just nvd -> do mmvd <- addVarDecl $ makeMonomorph nvd
					return $ fmap GenVarDecl mmvd
    in if isSimpleId v then
    do mk <- convertTypeToKind t
       case mk of 
	   Just k -> do addDiags [mkDiag Hint "is type variable" v]
			tv <- anaTypeVarDecl $ TypeArg v k s q
			return $ fmap GenTypeVarDecl tv 
           _ -> varDecl
    else varDecl

makeMonomorph :: VarDecl -> VarDecl
makeMonomorph (VarDecl v t sk ps) =
    let s = Map.fromList $ map ( \ a@(TypeArg i k _ _) -> 
				    (a, TypeName i k 0)) $ 
	    varsOf t
	in VarDecl v (repl s t) sk ps

-- | analyse 
anaVarDecl :: VarDecl -> State Env (Maybe VarDecl)
anaVarDecl(VarDecl v oldT sk ps) = 
    do mt <- anaStarType oldT
       return $ case mt of 
	       Nothing -> Nothing
	       Just t -> Just $ VarDecl v t sk ps

-- | add a local variable with an analysed type
addVarDecl :: VarDecl -> State Env (Maybe VarDecl) 
addVarDecl vd@(VarDecl v t _ _) = 
    do newV <- addOpId v (simpleTypeScheme t) [] VarDefn
       return $ fmap (const vd) newV

-- | get the variable
getVar :: VarDecl -> Id
getVar(VarDecl v _ _ _) = v

-- | check uniqueness of variables 
checkUniqueVars :: [VarDecl] -> State Env ()
checkUniqueVars = addDiags . checkUniqueness . map getVar

-- | check uniqueness of type variables 
checkUniqueTypevars :: [TypeArg] -> State Env ()
checkUniqueTypevars = addDiags . checkUniqueness 
		      . map getTypeVar

-- | filter out assumption
filterAssumps  :: (OpInfo -> Bool) -> Assumps -> Assumps
filterAssumps p =
    Map.filter (not . null . opInfos) .
       Map.map (OpInfos . filter p . opInfos)

-- | analyse types in typed patterns, and
-- create fresh type vars for unknown ids tagged with type MixfixType []. 
anaPattern :: Pattern -> State Env Pattern
anaPattern pat = 
    case pat of
    QualVar vd -> do newVd <- checkVarDecl vd
                     return $ QualVar newVd
    ResolvedMixTerm i pats ps -> do 
         l <- mapM anaPattern pats
	 return $ ResolvedMixTerm i l ps
    ApplTerm p1 p2 ps -> do
         p3 <- anaPattern p1
         p4 <- anaPattern p2
	 return $ ApplTerm p3 p4 ps
    TupleTerm pats ps -> do 
         l <- mapM anaPattern pats
	 return $ TupleTerm l ps
    TypedTerm p q ty ps -> do 
         mt <- anaStarType ty 
	 let newT = case mt of Just t -> t
			       _ -> ty
         case p of 
	     QualVar (VarDecl v (MixfixType []) ok qs) ->
		 let newVd = VarDecl v newT ok (qs ++ ps) in
		 return $ QualVar newVd
	     _ -> do newP <- anaPattern p
		     return $ TypedTerm newP q newT ps
    AsPattern vd p2 ps -> do
         newVd <- checkVarDecl vd
         p4 <- anaPattern p2
	 return $ AsPattern newVd p4 ps
    _ -> return pat
    where checkVarDecl vd@(VarDecl v t ok ps) = case t of 
	    MixfixType [] -> do
	        (tvar, c) <- toEnvState $ freshVar $ posOfVarDecl vd
		return $ VarDecl v (TypeName tvar star c) ok ps
	    _ -> do mt <- anaStarType t 
		    case mt of 
		        Just ty -> return $ VarDecl v ty ok ps 
		        _ -> return vd
