{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2003
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

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
       put $ e {envDiags = reverse ds ++ envDiags e}

-- | add sentences
appendSentences :: [Named Sentence] -> State Env ()
appendSentences fs =
    do e <- get
       put $ e {sentences = reverse fs ++ sentences e}

-- | store local assumptions
putLocalVars :: Map.Map Id Type -> State Env ()
putLocalVars vs =  do { e <- get; put e { localVars = vs } }

anaStarType :: Type -> State Env (Maybe Type)
anaStarType t = do mp <- fromResult $ anaStarTypeR t . typeMap
                   return $ fmap snd mp

anaInstTypes :: [Type] -> State Env [Type]
anaInstTypes ts = if null ts then return []
   else do mp <- fromResult $ anaType (Nothing, head ts) . typeMap
           rs <- anaInstTypes $ tail ts
           return $ case mp of
                   Nothing -> rs
                   Just (_, ty) -> ty:rs

anaTypeScheme :: TypeScheme -> State Env (Maybe TypeScheme)
anaTypeScheme (TypeScheme tArgs ty p) =
    do tm <- gets typeMap    -- save global variables  
       mArgs <- mapM anaddTypeVarDecl tArgs
       let newArgs = catMaybes mArgs  
       mt <- anaStarType ty
       putTypeMap tm       -- forget local variables 
       case mt of 
           Nothing -> return Nothing
           Just newTy -> do 
               let newSc = TypeScheme newArgs newTy p
               gTy <- if null newArgs then return $ generalize newSc 
                      else generalizeS newSc
               return $ Just gTy

generalizeS :: TypeScheme -> State Env TypeScheme
generalizeS sc = do 
    addDiags $ generalizable sc
    return $ generalize sc

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
                                 Result ds mDef = mergeTypeDefn defn d
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
anaddTypeVarDecl :: TypeArg -> State Env (Maybe TypeArg)
anaddTypeVarDecl(TypeArg t k s ps) = 
    case k of 
    MissingKind -> do 
       tk <- gets typeMap
       let rm = getIdKind tk t
       case maybeResult rm of 
              Nothing -> anaddTypeVarDecl(TypeArg t star s ps)
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

checkUnusedTypevars :: TypeScheme -> State Env TypeScheme
checkUnusedTypevars sc@(TypeScheme tArgs t ps) = do
    let ls = map snd $ leaves (< 0) t -- generic vars
        rest = tArgs List.\\ ls
    if null rest then return sc
      else do
      addDiags [mkDiag Warning "unused type variables" rest]
      return $ TypeScheme ls t ps

-- | storing an operation
addOpId :: UninstOpId -> TypeScheme -> [OpAttr] -> OpDefn 
        -> State Env (Maybe UninstOpId)
addOpId i oldSc attrs defn = 
    do sc <- checkUnusedTypevars oldSc
       e <- get
       let as = assumps e
           tm = typeMap e
           TypeScheme _ ty _ = sc 
           ds = if placeCount i > 1 then case unalias ty of 
                   FunType arg _ _ _ -> case unalias arg of
                       ProductType ts _ -> if placeCount i /= length ts then 
                            [mkDiag Error "wrong number of places in" i]
                            else [] 
                       _ -> [mkDiag Error "expected tuple argument for" i]
                   _ -> [mkDiag Error "expected function type for" i]
                 else []
           (l, r) = partitionOpId e i sc
           oInfo = OpInfo sc attrs defn 
       if null ds then 
               do let Result es mo = foldM (mergeOpInfo tm) oInfo l
                  addDiags $ map (improveDiag i) es
                  if i `elem` map fst bList then addDiags $ [mkDiag Warning
                      "ignoring declaration for builtin identifier" i]
                      else return ()
                  case mo of 
                      Nothing -> return Nothing
                      Just oi -> do putAssumps $ Map.insert i 
                                                   (OpInfos (oi : r)) as
                                    return $ Just i
          else do addDiags ds
                  return Nothing

----------------------------------------------------------------------------
-- local variables 
-----------------------------------------------------------------------------

-- | add a local variable with an analysed type (if True then warn)
addLocalVar :: Bool -> VarDecl -> State Env () 
addLocalVar b (VarDecl v t _ _) = 
    do ass <- gets assumps
       vs <- gets localVars
       if b then if Map.member v ass then
          addDiags [mkDiag Hint "variable shadows global name(s)" v]
          else if Map.member v vs then 
          addDiags [mkDiag Hint "shadowing by variable" v]
          else return ()
         else return ()  
       putLocalVars $ Map.insert v t vs 

-- | add a local variable with an analysed type
addGenLocalVar :: GenVarDecl -> State Env () 
addGenLocalVar d = case d of 
     GenVarDecl v -> addLocalVar False v
     GenTypeVarDecl t -> addTypeVarDecl False t >> return () 

----------------------------------------------------------------------------
-- GenVarDecl
-----------------------------------------------------------------------------

addGenVarDecl :: GenVarDecl -> State Env (Maybe GenVarDecl)
addGenVarDecl(GenVarDecl v) = do mv <- addVarDecl v
                                 return $ fmap GenVarDecl mv
addGenVarDecl(GenTypeVarDecl t) = do mt <- addTypeVarDecl True t 
                                     return $ fmap GenTypeVarDecl mt

-- | analyse and add global (True) or local variable or type declaration 
anaddGenVarDecl :: Bool -> GenVarDecl -> State Env (Maybe GenVarDecl)
anaddGenVarDecl b gv = case gv of 
    GenVarDecl v -> optAnaddVarDecl b v
    GenTypeVarDecl t -> anaddTypeVarDecl t >>= (return . fmap GenTypeVarDecl)

convertTypeToKind :: Monad m => ClassMap -> Type -> m Kind
convertTypeToKind cm ty = case ty of 
    FunType t1 FunArr t2 ps -> do 
        k1 <- convertTypeToKind cm t1
        k2 <- convertTypeToKind cm t2
        case k2 of 
            ExtKind _ _ _ -> fail "extended kind in result"
            _ -> return $ FunKind k1 k2 ps
    BracketType Parens [] _ -> fail "empty tuple"
    BracketType Parens [t] _ -> convertTypeToKind cm t
    BracketType Parens ts ps -> do 
        k:ks <- mapM (convertTypeToKind cm) ts
        let rk = rawKind k
        if all ((==rk) . rawKind) ks then
            return $ Intersection (k:ks) ps
            else fail "contradicting kinds of intersection"
    MixfixType [TypeToken t, t1] ->
        let s = tokStr t 
            mv = case s of 
                   "+" -> Just CoVar 
                   "-" -> Just ContraVar 
                   _ -> Nothing
        in case mv of 
              Nothing -> fail "no variance found"
              Just v -> do 
                  k1 <- convertTypeToKind cm t1
                  return $ ExtKind k1 v $ tokPos t
    TypeToken t -> 
       if tokStr t == "Type" then return $ Intersection [] $ tokPos t 
          else do
          let ci = simpleIdToId t
              rm = anaClassId ci cm
          case maybeResult rm of 
                  Nothing -> fail "class not found"
                  Just k -> return $ ClassKind ci k
    _ -> fail "wrong type construction"

-- | add global or local variable or type declaration (True means global)
optAnaddVarDecl :: Bool -> VarDecl -> State Env (Maybe GenVarDecl)
optAnaddVarDecl b vd@(VarDecl v t s q) = 
    let varDecl = do mvd <- anaVarDecl vd
                     case mvd of 
                         Nothing -> return Nothing
                         Just nvd -> let movd = makeMonomorph nvd in
                             if b then do 
                             mmvd <- addVarDecl movd
                             return $ fmap GenVarDecl mmvd
                             else do 
                             addLocalVar True movd
                             return $ Just $ GenVarDecl movd
    in if isSimpleId v then
    do cm <- gets classMap 
       let mk = convertTypeToKind cm t
       case mk of 
           Just k -> do addDiags [mkDiag Hint "is type variable" v]
                        tv <- anaddTypeVarDecl $ TypeArg v k s q
                        return $ fmap GenTypeVarDecl tv 
           _ -> varDecl
    else varDecl

makeMonomorph :: VarDecl -> VarDecl
makeMonomorph (VarDecl v t sk ps) = VarDecl v (monoType t) sk ps

monoType :: Type -> Type
monoType t = subst (Map.fromList $ 
                    map ( \ (v, TypeArg i k _ _) -> 
                          (v, TypeName i k 0)) $ leaves (> 0) t) t

-- | analyse variable declaration
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
                (tvar, c) <- toEnvState $ freshVar $ posOfId v
                return $ VarDecl v (TypeName tvar star c) ok ps
            _ -> do mt <- anaStarType t 
                    case mt of 
                        Just ty -> return $ VarDecl v ty ok ps 
                        _ -> return vd
