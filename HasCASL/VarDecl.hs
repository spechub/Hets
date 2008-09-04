{- |
Module      :  $Header$
Description :  analyse var decls
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

analyse generic var (or type var) decls

-}

module HasCASL.VarDecl where

import Data.Maybe
import Data.List as List
import Control.Monad
import Text.ParserCombinators.Parsec (runParser, eof)

import qualified Data.Map as Map
import qualified Data.Set as Set
import Common.Id
import Common.Lib.State
import Common.Result
import Common.DocUtils
import Common.Lexer
import Common.AnnoState

import HasCASL.ParseTerm
import HasCASL.As
import HasCASL.AsUtils
import HasCASL.FoldType
import HasCASL.Le
import HasCASL.PrintLe
import HasCASL.ClassAna
import HasCASL.TypeAna
import HasCASL.Unify
import HasCASL.Merge
import HasCASL.Builtin

anaStarType :: Type -> State Env (Maybe Type)
anaStarType t = fmap (fmap snd) $ anaType (Just universe, t)

anaType :: (Maybe Kind, Type)
        -> State Env (Maybe ((RawKind, Set.Set Kind), Type))
anaType p = fromResult $ anaTypeM p

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
                  Just (TypeVarDefn v vk rk c) ->
                      TypeArg i v vk rk c Other nullRange) svs
        newSc = TypeScheme (genTypeArgs newArgs) (generalize newArgs ty) p
    if null tArgs then return newSc
       else do
         addDiags $ generalizable False sc
         return newSc

-- | store type id and check kind arity (warn on redeclared types)
addTypeId :: Bool -> TypeDefn -> Kind -> Id -> State Env Bool
addTypeId warn dfn k i = do
    tvs <- gets localTypeVars
    case Map.lookup i tvs of
        Just _ -> do
            if warn then addDiags[mkDiag Warning
                                  "new type shadows type variable" i]
               else return ()
            putLocalTypeVars $ Map.delete i tvs
        Nothing -> return()
    cm <- gets classMap
    case Map.lookup i cm of
      Just _ -> do
          addDiags [mkDiag Error "class name used as type" i]
          return False
      Nothing -> addTypeKind warn dfn i k

-- | check if the kind only misses variance indicators of the known raw kind
isLiberalKind :: ClassMap -> Bool -> RawKind -> Kind -> Maybe Kind
isLiberalKind cm b ok k = case ok of
    ClassKind _ -> Just k
    FunKind ov fok aok _ -> case k of
        FunKind v fk ak ps -> do
            nfk <- isLiberalKind cm (not b) fok fk
            nak <- isLiberalKind cm b aok ak
            return $ FunKind (liberalVariance b ov v) nfk nak ps
        ClassKind i -> case Map.lookup i cm of
           Just ci -> maybe Nothing (const $ Just k) $ minRawKind "" ok
                      $ rawKind ci
           _ -> Nothing

liberalVariance :: Bool -> Variance -> Variance -> Variance
liberalVariance b v1 v2 = if b then minVariance v1 v2 else
       revVariance $ minVariance (revVariance v1) $ revVariance v2

-- | lifted 'anaKindM'
anaKind :: Kind -> State Env RawKind
anaKind k = do
    mrk <- fromResult $ anaKindM k . classMap
    case mrk of
      Nothing -> error "anaKind"
      Just rk -> return rk

-- | store type as is (warn on redeclared types)
addTypeKind :: Bool -> TypeDefn -> Id -> Kind -> State Env Bool
addTypeKind warn d i k = do
  e <- get
  rk <- anaKind k
  let tm = typeMap e
      cm = classMap e
      addTypeSym ck = if Map.member i bTypes then return () else
                         addSymbol $ idToTypeSymbol e i ck
  if placeCount i <= kindArity rk then return () else
      addDiags [mkDiag Error "wrong arity of" i]
  case Map.lookup i tm of
    Nothing -> do
      addTypeSym rk
      putTypeMap $ Map.insert i (TypeInfo rk (Set.singleton k) Set.empty d) tm
      return True
    Just (TypeInfo ok oldks sups dfn) ->
      case minRawKind "" ok rk of
      Nothing -> do
        addDiags $ diffKindDiag i ok rk
        return False
      Just r -> case isLiberalKind cm True r k of
       Just nk -> do
        let isNewInst = newKind cm nk oldks
            insts = if isNewInst then addNewKind cm nk oldks else oldks
            Result ds mDef = mergeTypeDefn dfn d
        if warn && not isNewInst && case (dfn, d) of
           (PreDatatype, DatatypeDefn _) -> False
           _ -> True
          then addDiags [mkDiag Hint "redeclared type" i]
          else return ()
        case mDef of
          Just newDefn -> do
            addTypeSym r
            putTypeMap $ Map.insert i (TypeInfo r insts sups newDefn) tm
            return True
          _ -> do
            addDiags $ map (improveDiag i) ds
            return False
       Nothing -> do
         addDiags [mkDiag Error "cannot refine kind" i]
         return False

nonUniqueKind :: (GetRange a, Pretty a) => Set.Set Kind -> a ->
                 (Kind -> State Env (Maybe b)) -> State Env (Maybe b)
nonUniqueKind ks a f = case Set.toList ks of
    [k] -> f k
    _ -> do addDiags [mkDiag Error "non-unique kind for" a]
            return Nothing

-- | analyse a type argument
anaddTypeVarDecl :: TypeArg -> State Env (Maybe TypeArg)
anaddTypeVarDecl (TypeArg i v vk _ _ s ps) = do
  cm <- gets classMap
  case Map.lookup i cm of
    Just _ -> do
        addDiags [mkDiag Error "class used as type variable" i]
        return Nothing
    Nothing -> do
     c <- toEnvState inc
     case vk of
      VarKind k ->
        let Result ds (Just rk) = anaKindM k cm
        in if null ds then do
            addLocalTypeVar True (TypeVarDefn v vk rk c) i
            return $ Just $ TypeArg i v vk rk c s ps
        else do addDiags ds
                return Nothing
      Downset t -> do
        mt <- anaType (Nothing, t)
        case mt of
            Nothing -> return Nothing
            Just ((rk, ks), nt) ->
                nonUniqueKind ks t $ \ k -> do
                   let nd = Downset (KindedType nt (Set.singleton k) nullRange)
                   addLocalTypeVar True (TypeVarDefn NonVar nd rk c) i
                   return $ Just $ TypeArg i v (Downset nt) rk c s ps
      MissingKind -> do
        tvs <- gets localTypeVars
        case Map.lookup i tvs of
            Nothing -> do
                addDiags [mkDiag Error "unknown type variable" i]
                let dvk = VarKind universe
                addLocalTypeVar True (TypeVarDefn v dvk rStar c) i
                return $ Just $ TypeArg i v dvk rStar c s ps
            Just (TypeVarDefn v0 dvk rk _) -> do
                addLocalTypeVar False (TypeVarDefn v0 dvk rk c) i
                return $ Just $ TypeArg i v0 dvk rk c s ps

-- | partition information of an uninstantiated identifier
partitionOpId :: Env -> Id -> TypeScheme -> (Set.Set OpInfo, Set.Set OpInfo)
partitionOpId e i sc =
    Set.partition ((sc ==) . opType)
           $ Map.findWithDefault Set.empty i $ assumps e

checkUnusedTypevars :: TypeScheme -> State Env TypeScheme
checkUnusedTypevars sc@(TypeScheme tArgs t ps) = do
    let ls = map (fst . snd) $ leaves (< 0) t -- generic vars
        rest = map getTypeVar tArgs List.\\ ls
    if null rest then return ()
      else addDiags [Diag Warning ("unused type variables: "
               ++ show(ppWithCommas rest)) ps]
    return sc

checkPlaceCount :: Env -> Id -> TypeScheme -> [Diagnosis]
checkPlaceCount e i (TypeScheme _ ty _) =
    if placeCount i > 1 then
        let (fty, fargs) = getTypeAppl ty in
        if length fargs == 2 && lesserType e fty (toFunType PFunArr) then
            let (pty, ts) = getTypeAppl (head fargs)
                n = length ts in
            if n > 1 && lesserType e pty (toProdType n nullRange) then
                if placeCount i /= n then
                    [mkDiag Warning "wrong number of places in" i]
                else []
            else [mkDiag Warning "expected tuple argument for" i]
        else [mkDiag Warning "expected function type for" i]
    else []

-- | storing an operation
addOpId :: Id -> TypeScheme -> Set.Set OpAttr -> OpDefn -> State Env Bool
addOpId i oldSc attrs dfn = do
    sc@(TypeScheme _ ty _) <- checkUnusedTypevars oldSc
    e <- get
    let as = assumps e
        bs = binders e
        ds = checkPlaceCount e i sc
        (l, r) = partitionOpId e i sc
        oInfo = OpInfo sc attrs dfn
        Result es mo = foldM mergeOpInfo oInfo $ Set.toList l
    addDiags ds
    addDiags $ map (improveDiag i) es
    if i `elem` map fst bList then
      addDiags [mkDiag Warning "ignoring declaration for builtin identifier" i]
      else unless (Set.null l) $ addDiags
      [mkDiag Hint ("repeated declaration of '" ++ showId i "' with type") ty]
    when (Map.member i bs) $ do
      addDiags [mkDiag Warning "identifier shadows binder" i]
      putBinders $ Map.delete i bs
    case mo of
      Nothing -> return False
      Just oi -> do
        addSymbol $ idToOpSymbol e i $ opType oi
        putAssumps $ Map.insert i (Set.insert oi r) as
        return True

-- | add a local variable with an analysed type (if True then warn)
addLocalVar :: Bool -> VarDecl -> State Env ()
addLocalVar warn (VarDecl v t _ _) =
    do e <- get
       let vs = localVars e
       when warn $ do
         when (Map.member v $ assumps e)
           $ addDiags [mkDiag Hint "variable shadows global name(s)" v]
         when (Map.member v vs)
           $ addDiags [mkDiag Hint "rebound variable" v]
         when (Map.member v $ localTypeVars e)
           $ addDiags [mkDiag Hint "variable also known as type variable" v]
       putLocalVars $ Map.insert v (VarDefn t) vs

-- | add analysed local variable or type variable declaration
addGenVarDecl :: GenVarDecl -> State Env ()
addGenVarDecl(GenVarDecl v) = addLocalVar True v
addGenVarDecl(GenTypeVarDecl t) = addTypeVarDecl False t

-- | analyse and add local variable or type variable declaration
anaddGenVarDecl :: Bool -> GenVarDecl -> State Env (Maybe GenVarDecl)
anaddGenVarDecl warn gv = case gv of
    GenVarDecl v -> optAnaddVarDecl warn v
    GenTypeVarDecl t -> anaddTypeVarDecl t >>= (return . fmap GenTypeVarDecl)

convTypeToKind :: Type -> Maybe (Variance, Kind)
convTypeToKind ty = let s = showDoc ty "" in
    case runParser (extKind << eof) (emptyAnnos ()) "" s of
    Right (v, k) -> Just (v, k)
    _ -> Nothing

convertTypeToKind :: Env -> Type -> Result (Variance, Kind)
convertTypeToKind e ty =  case convTypeToKind ty of
    Just (v, k) -> let Result ds _ = anaKindM k $ classMap e in
               if null ds then return (v, k) else Result ds Nothing
    _ -> fail $ "not a kind '" ++ showDoc ty "'"

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
           Just (vv, k) -> do
               addDiags [mkDiag Hint "is type variable" v]
               tv <- anaddTypeVarDecl $ TypeArg v vv (VarKind k) rStar 0 s q
               return $ fmap GenTypeVarDecl tv
           _ -> do addDiags $ map ( \ d -> Diag Hint (diagString d) q) ds
                   varDecl
    else varDecl

makeMonomorph :: VarDecl -> VarDecl
makeMonomorph (VarDecl v t sk ps) = VarDecl v (monoType t) sk ps

monoType :: Type -> Type
monoType = foldType mapTypeRec
  { foldTypeName = \ t i k n -> if n > 0 then TypeName i k 0 else t }

-- | analyse variable declaration
anaVarDecl :: VarDecl -> State Env (Maybe VarDecl)
anaVarDecl(VarDecl v oldT sk ps) =
    do mt <- anaStarType oldT
       return $ case mt of
               Nothing -> Nothing
               Just t -> Just $ VarDecl v t sk ps
