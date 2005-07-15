{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2005
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
import Common.Id
import Common.AS_Annotation
import Common.Lib.State
import Common.Result
import Common.PrettyPrint
import Common.Lexer
import Common.AnnoState
import Text.ParserCombinators.Parsec (runParser, eof)

import HasCASL.ParseTerm
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
       put $ e {envDiags = reverse ds ++ envDiags e}

-- | add sentences
appendSentences :: [Named Sentence] -> State Env ()
appendSentences fs =
    do e <- get
       put $ e {sentences = reverse fs ++ sentences e}

-- | store local assumptions
putLocalVars :: Map.Map Id VarDefn -> State Env ()
putLocalVars vs =  do { e <- get; put e { localVars = vs } }

anaStarType :: Type -> State Env (Maybe Type)
anaStarType t = fmap (fmap snd) $ anaType (Just star, t) 

anaType :: (Maybe Kind, Type)  -> State Env (Maybe ((RawKind, [Kind]), Type))
anaType p = fromResult $ anaTypeM p

anaInstTypes :: [Type] -> State Env [Type]
anaInstTypes ts = if null ts then return []
   else do mp <- anaType (Nothing, head ts) 
           rs <- anaInstTypes $ tail ts
           return $ case mp of
                   Nothing -> rs
                   Just (_, ty) -> ty:rs

anaTypeScheme :: TypeScheme -> State Env (Maybe TypeScheme)
anaTypeScheme (TypeScheme tArgs ty p) =
    do tvs <- gets localTypeVars    -- save global variables  
       mArgs <- mapM anaddTypeVarDecl tArgs
       let newArgs = catMaybes mArgs  
       mt <- anaStarType ty
       case mt of 
           Nothing -> do putLocalTypeVars tvs       -- forget local variables 
                         return Nothing
           Just newTy -> do 
               let newSc = TypeScheme newArgs newTy p
               gTy <- generalizeS newSc
               putLocalTypeVars tvs       -- forget local variables 
               return $ Just gTy

generalizeS :: TypeScheme -> State Env TypeScheme
generalizeS sc@(TypeScheme tArgs ty p) = do 
    let fvs = leaves (> 0) ty
        svs = sortBy comp fvs
        comp a b = compare (fst a) $ fst b
    tvs <- gets localTypeVars 
    let newArgs = map ( \ (_, (i, _)) -> case Map.lookup i tvs of
                  Nothing -> error "generalizeS" 
                  Just (TypeVarDefn rk vk c) -> 
                      TypeArg i vk rk c Other nullRange) svs
        newTy = generalize newArgs ty
    if null tArgs then return $ TypeScheme newArgs newTy p
       else do
         addDiags $ generalizable sc
         return $ TypeScheme newArgs newTy p

anaKind :: Kind -> State Env RawKind
anaKind k = do mrk <- fromResult $ anaKindM k . classMap
               case mrk of 
                   Nothing -> error "anaKind"
                   Just rk -> return rk

fromResult :: (Env -> Result a) -> State Env (Maybe a)
fromResult f = do 
   e <- get
   let Result ds mr = f e
   addDiags ds
   return mr

-- ---------------------------------------------------------------------------
-- storing type ids with their kind and definition
-- ---------------------------------------------------------------------------

-- | store local type variables
putLocalTypeVars :: LocalTypeVars -> State Env ()
putLocalTypeVars tvs = do 
    e <- get 
    put e { localTypeVars = tvs }

addLocalTypeVar :: Bool -> TypeVarDefn -> Id -> State Env ()
addLocalTypeVar warn tvd i = do 
    tvs <- gets localTypeVars
    if warn then do 
         tm <- gets typeMap
         case Map.lookup i tm of 
             Nothing -> case Map.lookup i tvs of 
                 Nothing -> return ()
                 Just _ -> addDiags [mkDiag Hint "rebound type variable" i] 
             Just _ -> addDiags [mkDiag Hint 
                    "type variable shadows type constructor" i]
       else return ()
    putLocalTypeVars $ Map.insert i tvd tvs

-- | store a complete type map
putTypeMap :: TypeMap -> State Env ()
putTypeMap tm = do 
    e <- get 
    put e { typeMap = tm }

-- | store type id and check kind arity (warn on redeclared types)
addTypeId :: Bool -> TypeDefn -> Instance -> RawKind -> Kind -> Id 
          -> State Env Bool
addTypeId warn defn _ rk k i = 
    do if placeCount i <= kindArity rk then do
          addTypeKind warn defn i rk k
          return True
          else do addDiags [mkDiag Error "wrong arity of" i]
                  return False

-- | store type as is (warn on redeclared types)
addTypeKind :: Bool -> TypeDefn -> Id -> RawKind -> Kind -> State Env Bool
addTypeKind warn d i rk k = 
    do tm <- gets typeMap
       case Map.lookup i tm of
           Nothing -> do 
               putTypeMap $ Map.insert i (TypeInfo rk [k] [] d) tm
               return True 
           Just (TypeInfo ok oldks sups defn) -> 
               if rk == ok then do 
                   let isKnownInst = k `elem` oldks
                       insts = if isKnownInst then oldks else k : oldks
                       Result ds mDef = mergeTypeDefn defn d
                   if warn && isKnownInst && case (defn, d) of 
                                 (PreDatatype, DatatypeDefn _) -> False
                                 _ -> True then
                       addDiags [mkDiag Hint "redeclared type" i]
                       else return ()
                   case mDef of
                       Just newDefn -> do 
                           putTypeMap $ Map.insert i 
                               (TypeInfo ok insts sups newDefn) tm
                           return True
                       Nothing -> do 
                           addDiags $ map (improveDiag i) ds
                           return False
                else do addDiags $ diffKindDiag i ok rk 
                        return False

nonUniqueKind :: (PosItem a, PrettyPrint a) => [Kind] -> a -> 
                 (Kind -> State Env (Maybe b)) -> State Env (Maybe b)
nonUniqueKind ks a f = case ks of
    [k] -> f k
    _ -> do addDiags [mkDiag Error "non-unique kind for" a]
            return Nothing

-- | analyse a type argument 
anaddTypeVarDecl :: TypeArg -> State Env (Maybe TypeArg)
anaddTypeVarDecl (TypeArg i vk _ _ s ps) = do
    c <- toEnvState inc
    case vk of 
      VarKind k -> do 
        rk <- anaKind k
        addLocalTypeVar True (TypeVarDefn rk vk c) i
        return $ Just $ TypeArg i vk rk c s ps
      Downset t -> do                 
        mt <- anaType (Nothing, t)
        case mt of 
            Nothing -> return Nothing
            Just ((rk, ks), nt) -> 
                nonUniqueKind ks t $ \ k -> do
                   let nd = Downset (KindedType nt k nullRange)
                   addLocalTypeVar True (TypeVarDefn rk nd c) i
                   return $ Just $ TypeArg i (Downset nt) rk c s ps
      MissingKind -> do 
        tvs <- gets localTypeVars
        case Map.lookup i tvs of 
            Nothing -> do 
                addDiags [mkDiag Warning "missing kind for type variable " i]
                let dvk = VarKind star
                addLocalTypeVar True (TypeVarDefn star dvk c) i
                return $ Just $ TypeArg i dvk star c s ps
            Just (TypeVarDefn rk dvk _) -> do 
                addLocalTypeVar True (TypeVarDefn rk dvk c) i
                return $ Just $ TypeArg i dvk rk c s ps

-- | add an analysed type argument (warn on redeclared types)
addTypeVarDecl :: Bool -> TypeArg -> State Env ()
addTypeVarDecl warn (TypeArg i vk rk c _ _) = 
       addLocalTypeVar warn (TypeVarDefn rk vk c) i

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
checkUnusedTypevars sc@(TypeScheme tArgs t _) = do
    let ls = map (fst . snd) $ leaves (< 0) t -- generic vars
        rest = map getTypeVar tArgs List.\\ ls
    if null rest then return ()
      else addDiags [mkDiag Warning "unused type variables" rest]
    return sc

-- | storing an operation
addOpId :: UninstOpId -> TypeScheme -> [OpAttr] -> OpDefn 
        -> State Env Bool
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
                      Nothing -> return False
                      Just oi -> do putAssumps $ Map.insert i 
                                                   (OpInfos (oi : r)) as
                                    return True
          else do addDiags ds
                  return False

----------------------------------------------------------------------------
-- local variables 
-----------------------------------------------------------------------------

-- | add a local variable with an analysed type (if True then warn)
addLocalVar :: Bool -> VarDecl -> State Env () 
addLocalVar warn (VarDecl v t _ _) = 
    do ass <- gets assumps
       vs <- gets localVars
       if warn then if Map.member v ass then
          addDiags [mkDiag Hint "variable shadows global name(s)" v]
          else if Map.member v vs then 
          addDiags [mkDiag Hint "rebound variable" v]
          else return ()
         else return ()  
       putLocalVars $ Map.insert v (VarDefn t) vs 

----------------------------------------------------------------------------
-- GenVarDecl
-----------------------------------------------------------------------------

-- | add analysed local variable or type variable declaration 
addGenVarDecl :: GenVarDecl -> State Env ()
addGenVarDecl(GenVarDecl v) = addLocalVar True v
addGenVarDecl(GenTypeVarDecl t) = addTypeVarDecl False t 

-- | analyse and add local variable or type variable declaration 
anaddGenVarDecl :: Bool -> GenVarDecl -> State Env (Maybe GenVarDecl)
anaddGenVarDecl warn gv = case gv of 
    GenVarDecl v -> optAnaddVarDecl warn v
    GenTypeVarDecl t -> anaddTypeVarDecl t >>= (return . fmap GenTypeVarDecl)

convertTypeToKind :: Env -> Type -> Result Kind
convertTypeToKind e ty = let s = showPretty ty "" in
    case runParser (extKind << eof) (emptyAnnos ()) "" s of
    Right k -> let Result ds _ = anaKindM k $ classMap e in
               if null ds then return k else Result ds Nothing
    Left _ -> fail $ "not a kind '" ++ s ++ "'"

-- | local variable or type variable declaration
optAnaddVarDecl :: Bool -> VarDecl -> State Env (Maybe GenVarDecl)
optAnaddVarDecl warn vd@(VarDecl v t s q) = 
    let varDecl = do mvd <- anaVarDecl vd
                     case mvd of 
                         Nothing -> return Nothing
                         Just nvd -> do 
                             let movd = makeMonomorph nvd 
                             addLocalVar warn movd
                             return $ Just $ GenVarDecl movd
    in if isSimpleId v then
    do e <- get
       let Result ds mk = convertTypeToKind e t
       case mk of 
           Just k -> do 
               addDiags [mkDiag Hint "is type variable" v]
               tv <- anaddTypeVarDecl $ TypeArg v (VarKind k) star 0 s q
               return $ fmap GenTypeVarDecl tv 
           _ -> do addDiags $ map ( \ d -> Diag Hint (diagString d) q) ds  
                   varDecl
    else varDecl

makeMonomorph :: VarDecl -> VarDecl
makeMonomorph (VarDecl v t sk ps) = VarDecl v (monoType t) sk ps

monoType :: Type -> Type
monoType t = subst (Map.fromList $ 
                    map ( \ (v, (i, rk)) -> 
                          (v, TypeName i rk 0)) $ leaves (> 0) t) t

-- | analyse variable declaration
anaVarDecl :: VarDecl -> State Env (Maybe VarDecl)
anaVarDecl(VarDecl v oldT sk ps) = 
    do mt <- anaStarType oldT
       return $ case mt of 
               Nothing -> Nothing
               Just t -> Just $ VarDecl v t sk ps

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
                 let newVd = VarDecl v newT ok (qs `appRange` ps) in
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
