{- |
Module      :  $Header$
Description :  analyse type declarations
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

analyse type declarations
-}

module HasCASL.TypeDecl
    ( anaFormula
    , mapAnMaybe
    , anaTypeItems
    , dataPatToType
    , ana1Datatype
    , anaDatatype
    , addDataSen
    ) where

import Data.Maybe
import Data.List(group)

import Common.Id
import Common.AS_Annotation
import Common.Lib.State
import qualified Data.Map as Map
import qualified Data.Set as Set
import Common.Result

import HasCASL.As
import HasCASL.AsUtils
import HasCASL.Builtin
import HasCASL.Le
import HasCASL.ClassAna
import HasCASL.TypeAna
import HasCASL.ConvertTypePattern
import HasCASL.DataAna
import HasCASL.Unify
import HasCASL.VarDecl
import HasCASL.SubtypeDecl
import HasCASL.MixAna
import HasCASL.TypeCheck

-- | resolve and type check a formula
anaFormula :: Annoted Term -> State Env (Maybe (Annoted Term, Annoted Term))
anaFormula at = do
    rt <- resolve $ item at
    case rt of
      Nothing -> return Nothing
      Just t -> do
          mt <- typeCheck (Just unitType) t
          return $ case mt of
              Nothing -> Nothing
              Just e -> Just (at { item = t }, at { item = e })

anaVars :: Env -> Vars -> Type -> Result Term
anaVars te vv t = case vv of
    Var v -> return $ QualVar $ VarDecl v t Other $ posOfId v
    VarTuple vs ps -> let
        (topTy, ts) = getTypeAppl t
        n = length ts in
        if n > 1 && lesserType te topTy (toProdType n nullRange) then
               if n == length vs then
                  let lrs = zipWith (anaVars te) vs ts
                      lms = map maybeResult lrs in
                      if all isJust lms then
                         return $ TupleTerm (map fromJust lms) ps
                         else Result (concatMap diags lrs) Nothing
               else mkError "wrong arity" topTy
        else mkError "product type expected" topTy

-- | lift a analysis function to annotated items
mapAnMaybe :: (Monad m) => (Annoted a -> m (Maybe b)) -> [Annoted a]
           -> m [Annoted b]
mapAnMaybe f al = do
    il <- mapM f al
    return $ map ( \ (i, a) -> replaceAnnoted (fromJust i) a) $
           filter (isJust . fst) $ zip il al

-- | analyse annotated type items
anaTypeItems :: GenKind -> [Annoted TypeItem] -> State Env [Annoted TypeItem]
anaTypeItems gk l = do
    ul <- mapAnMaybe ana1TypeItem l
    tys <- mapM ( \ (Datatype d) -> dataPatToType d) $
              filter ( \ t -> case t of
                       Datatype _ -> True
                       _ -> False) $ map item ul
    rl <- mapAnMaybe (anaTypeItem gk tys) ul
    addDataSen tys
    return rl

-- | add sentences for data type definitions
addDataSen :: [DataPat] -> State Env ()
addDataSen tys = do
    tm <- gets typeMap
    let tis = map ( \ (DataPat i _ _ _) -> i) tys
        ds = foldr ( \ i dl -> case Map.lookup i tm of
                     Nothing -> dl
                     Just ti -> case typeDefn ti of
                                DatatypeDefn dd -> dd : dl
                                _ -> dl) [] tis
        sen = (makeNamed ("ga_" ++ showSepList (showString "_") showId tis "")
              $ DatatypeSen ds) { isDef = True }
    if null tys then return () else appendSentences [sen]

ana1TypeItem :: Annoted TypeItem -> State Env (Maybe TypeItem)
ana1TypeItem t = case item t of
    Datatype d -> do
        md <- ana1Datatype $ replaceAnnoted d t
        return $ fmap Datatype md
    i -> return $ Just i

anaTypeDecl :: [TypePattern] -> Kind -> Range -> State Env (Maybe TypeItem)
anaTypeDecl pats kind ps = do
    cm <- gets classMap
    let Result cs _ = anaKindM kind cm
        Result ds (Just is) = convertTypePatterns pats
    addDiags $ cs ++ ds
    let ak = if null cs then kind else universe
    mis <- mapM (addTypePattern NoTypeDefn ak) is
    let newPats = map toTypePattern $ catMaybes mis
    return $ if null newPats then Nothing else Just $ TypeDecl newPats ak ps

anaIsoDecl :: [TypePattern] -> Range -> State Env (Maybe TypeItem)
anaIsoDecl pats ps = do
    let Result ds (Just is) = convertTypePatterns pats
    addDiags ds
    mis <- mapM (addTypePattern NoTypeDefn universe) is
    case catMaybes mis of
      [] -> return Nothing
      nis -> do
        let (i, _) : ris = reverse nis
        mapM_ (\ (j, _) -> addAliasType False j
              (TypeScheme [] (TypeName i rStar 0) $ posOfId j) universe) ris
        return $ Just $ IsoDecl (map toTypePattern nis) ps

setTypePatternVars :: [(Id, [TypeArg])] -> State Env [(Id, [TypeArg])]
setTypePatternVars ol = do
    l <- mapM ( \ (i, tArgs) -> do
            e <- get
            newAs <- mapM anaddTypeVarDecl tArgs
            put e
            return (i, catMaybes newAs)) ol
    let g = group $ map snd l
    case g of
      [_ : _] -> do
         newAs <- mapM anaddTypeVarDecl $ snd $ head l
         return $ map ( \ (i, _) -> (i, catMaybes newAs)) l
      _ -> do
        addDiags [mkDiag Error
            "variables must be identical for all types within one item" l]
        return []

anaSubtypeDecl :: [TypePattern] -> Type -> Range -> State Env (Maybe TypeItem)
anaSubtypeDecl pats t ps = do
    let Result ds (Just is) = convertTypePatterns pats
    addDiags ds
    tvs <- gets localTypeVars
    nis <- setTypePatternVars is
    let newPats = map toTypePattern nis
    te <- get
    putLocalTypeVars tvs
    let Result es mp = anaTypeM (Nothing, t) te
    case mp of
      Nothing -> do
        mapM_ (addTypePattern NoTypeDefn universe) is
        if null newPats then return Nothing else case t of
            TypeToken tt -> do
                let tid = simpleIdToId tt
                    newT = TypeName tid rStar 0
                addTypeId False NoTypeDefn universe tid
                mapM_ (addSuperType newT universe) nis
                return $ Just $ SubtypeDecl newPats newT ps
            _ -> do
                addDiags es
                return $ Just $ TypeDecl newPats universe ps
      Just ((rk, ks), newT) -> nonUniqueKind ks rk t $ \ kind -> do
          mapM_ (addTypePattern NoTypeDefn kind) is
          mapM_ (addSuperType newT $ rawToKind rk) nis
          return $ if null nis then Nothing else
                       Just $ SubtypeDecl newPats newT ps

anaSubtypeDefn :: Annoted TypeItem -> TypePattern -> Vars -> Type
               -> (Annoted Term) -> Range -> State Env (Maybe TypeItem)
anaSubtypeDefn aitm pat v t f ps = do
    let Result ds m = convertTypePattern pat
    addDiags ds
    case m of
      Nothing -> return Nothing
      Just (i, tArgs) -> do
        tvs <- gets localTypeVars
        newAs <- mapM anaddTypeVarDecl tArgs
        mt <- anaStarType t
        putLocalTypeVars tvs
        case mt of
          Nothing -> return Nothing
          Just ty -> do
            let nAs = catMaybes newAs
                fullKind = typeArgsListToKind nAs universe
                jTy = TypeName i (typeArgsListToRawKind nAs rStar) 0
                aTy = mkTypeAppl jTy $ map typeArgToType nAs
            e <- get
            let Result es mvds = anaVars e v $ monoType ty
            addDiags es
            if cyclicType i ty then do
                addDiags [mkDiag Error
                          "illegal recursive subtype definition" ty]
                return Nothing
              else case mvds of
                Nothing -> return Nothing
                Just vtt -> do
                  let vds = extractVars vtt
                  checkUniqueVars vds
                  vs <- gets localVars
                  mapM_ (addLocalVar True) vds
                  mf <- anaFormula f
                  putLocalVars vs
                  case mf of
                    Nothing -> return Nothing
                    Just (newF, resF) -> do
                      addTypeId True NoTypeDefn fullKind i
                      addSuperType ty universe (i, nAs)
                      let lab1 = getRLabel resF
                          lab = if null lab1 then getRLabel aitm else lab1
                      appendSentences [makeNamed lab
                        $ Formula $ mkEnvForall e (
                              mkForall (map GenVarDecl vds)
                              $ mkLogTerm eqvId ps
                              (TypedTerm vtt InType aTy ps) $ item resF) ps]
                      return $ Just $ SubtypeDefn (TypePattern i nAs nullRange)
                                    v ty newF ps

anaAliasType :: TypePattern -> Maybe Kind -> TypeScheme
             -> Range -> State Env (Maybe TypeItem)
anaAliasType pat mk sc ps = do
    let Result ds m = convertTypePattern pat
    addDiags ds
    case m of
      Nothing -> return Nothing
      Just (i, tArgs) -> do
        tvs <- gets localTypeVars -- save variables
        newAs <- mapM anaddTypeVarDecl tArgs
        (ik, mt) <- anaPseudoType mk sc
        putLocalTypeVars tvs
        case mt of
          Nothing -> return Nothing
          Just (TypeScheme args ty qs) ->
            if cyclicType i ty then do
                addDiags [mkDiag Error "illegal recursive type synonym" ty]
                return Nothing
              else do
                let nAs = catMaybes newAs
                    allArgs = nAs ++ args
                    fullKind = typeArgsListToKind nAs ik
                    allSc = TypeScheme allArgs ty qs
                b <- addAliasType True i allSc fullKind
                tm <- gets typeMap
                putTypeMap $ Map.map ( \ ti -> case typeDefn ti of
                    AliasTypeDefn y -> ti
                      { typeDefn = AliasTypeDefn $ expandAux tm y }
                    _ -> ti) tm
                return $ if b then Just $ AliasType
                    (TypePattern i [] nullRange) (Just fullKind) allSc ps
                         else Nothing

-- | analyse a 'TypeItem'
anaTypeItem :: GenKind -> [DataPat] -> Annoted TypeItem
            -> State Env (Maybe TypeItem)
anaTypeItem gk tys aitm = case item aitm of
    TypeDecl pats kind ps -> anaTypeDecl pats kind ps
    SubtypeDecl pats t ps -> anaSubtypeDecl pats t ps
    IsoDecl pats ps -> anaIsoDecl pats ps
    SubtypeDefn pat v t f ps -> anaSubtypeDefn aitm pat v t f ps
    AliasType pat mk sc ps -> anaAliasType pat mk sc ps
    Datatype d -> do
        mD <- anaDatatype gk tys $ replaceAnnoted d aitm
        case mD of
          Nothing -> return Nothing
          Just newD -> return $ Just $ Datatype newD

-- | pre-analyse a data type for 'anaDatatype'
ana1Datatype :: Annoted DatatypeDecl -> State Env (Maybe DatatypeDecl)
ana1Datatype aitm = do
    let DatatypeDecl pat kind alts derivs ps = item aitm
    cm <- gets classMap
    let Result cs (Just rk) = anaKindM kind cm
        k = if null cs then kind else universe
    addDiags $ checkKinds pat rStar rk ++ cs
    let rms = map ( \ c -> anaKindM (ClassKind c) cm) derivs
        mcs = map maybeResult rms
        jcs = catMaybes mcs
        newDerivs = map fst $ filter (isJust . snd) $ zip derivs mcs
        Result ds m = convertTypePattern pat
    addDiags (ds ++ concatMap diags rms)
    addDiags $ concatMap (checkKinds pat rStar) jcs
    case m of
      Nothing -> return Nothing
      Just (i, tArgs) -> do
          tvs <- gets localTypeVars
          newAs <- mapM anaddTypeVarDecl tArgs
          putLocalTypeVars tvs
          let nAs = catMaybes newAs
              fullKind = typeArgsListToKind nAs k
          addDiags $ checkUniqueTypevars nAs
          b <- addTypeId False PreDatatype fullKind i
          return $ if b then Just $ DatatypeDecl
                     (TypePattern i nAs nullRange) k alts newDerivs ps
                   else Nothing

-- | convert a data type with an analysed type pattern to a data pattern
dataPatToType :: DatatypeDecl -> State Env DataPat
dataPatToType d = case d of
    DatatypeDecl (TypePattern i nAs _) k _ _ _ -> do
      rk <- anaKind k
      return $ DataPat i nAs rk $ patToType i nAs rk
    _ -> error "dataPatToType"

addDataSubtype :: DataPat -> Kind -> Type -> State Env ()
addDataSubtype (DataPat _ nAs _ rt) k st = case st of
    TypeName i _ _ -> addSuperType rt k (i, nAs)
    _ -> addDiags [mkDiag Warning "data subtype ignored" st]

-- | analyse a pre-analysed data type given all data patterns of the type item
anaDatatype :: GenKind -> [DataPat]
            -> Annoted DatatypeDecl -> State Env (Maybe DatatypeDecl)
anaDatatype genKind tys d = case item d of
    itd@(DatatypeDecl (TypePattern i nAs _) k alts _ _) -> do
       -- recompute data pattern rather than looking it up in tys
       dt@(DataPat _ _ rk _) <- dataPatToType itd
       let fullKind = typeArgsListToKind nAs k
       tvs <- gets localTypeVars
       mapM_ (addTypeVarDecl False) $ map nonVarTypeArg nAs
       mNewAlts <- fromResult $ anaAlts tys dt (map item alts)
       putLocalTypeVars tvs
       case mNewAlts of
         Nothing -> return Nothing
         Just newAlts -> do
           mapM_ (addDataSubtype dt fullKind) $ foldr
             ( \ (Construct mc ts _ _) l -> case mc of
               Nothing -> ts ++ l
               Just _ -> l) [] newAlts
           let gArgs = genTypeArgs nAs
               de = DataEntry Map.empty i genKind gArgs rk
                    $ Set.fromList newAlts
               dp = toDataPat de
           mapM_ ( \ (Construct mc tc p sels) -> case mc of
               Nothing -> return ()
               Just c -> do
                 let sc = getConstrScheme dp p tc
                 addOpId c sc Set.empty (ConstructData i)
                 mapM_ ( \ (Select ms ts pa) -> case ms of
                   Just s ->
                     addOpId s (getSelScheme dp pa ts) Set.empty $ SelectData
                         (Set.singleton $ ConstrInfo c sc) i
                   Nothing -> return False) $ concat sels) newAlts
           addTypeId True (DatatypeDefn de) fullKind i
           appendSentences $ makeDataSelEqs dp newAlts
           return $ Just itd
    _ -> error "anaDatatype (not preprocessed)"

-- | analyse a pseudo type (represented as a 'TypeScheme')
anaPseudoType :: Maybe Kind -> TypeScheme -> State Env (Kind, Maybe TypeScheme)
anaPseudoType mk (TypeScheme tArgs ty p) = do
    cm <- gets classMap
    let k = case mk of
              Nothing -> Nothing
              Just j -> let Result cs _ = anaKindM j cm
                        in Just $ if null cs then j else universe
    nAs <- mapM anaddTypeVarDecl tArgs
    let ntArgs = catMaybes nAs
    mp <- anaType (Nothing, ty)
    case mp of
      Nothing -> return (universe, Nothing)
      Just ((_, sks), newTy) -> case Set.toList sks of
        [sk] -> do
          let newK = typeArgsListToKind ntArgs sk
          irk <- anaKind newK
          case k of
            Nothing -> return ()
            Just j -> do
              grk <- anaKind j
              addDiags $ checkKinds ty grk irk
          return (newK, Just $ TypeScheme ntArgs newTy p)
        _ -> return (universe, Nothing)

-- | add a type pattern
addTypePattern :: TypeDefn -> Kind -> (Id, [TypeArg])
               -> State Env (Maybe (Id, [TypeArg]))
addTypePattern defn kind (i, tArgs) = do
        tvs <- gets localTypeVars
        newAs <- mapM anaddTypeVarDecl tArgs
        putLocalTypeVars tvs
        let nAs = catMaybes newAs
            fullKind = typeArgsListToKind nAs kind
        addDiags $ checkUniqueTypevars nAs
        b <- addTypeId True defn fullKind i
        return $ if b then Just (i, nAs) else Nothing
