{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable
    
analyse type decls

-}

module HasCASL.TypeDecl where

import Data.Maybe

import Common.Lexer
import Common.Id
import Common.AS_Annotation
import Common.Lib.State
import qualified Common.Lib.Map as Map
import Common.Result
import Common.GlobalAnnotations

import HasCASL.As
import HasCASL.Le
import HasCASL.ClassAna
import HasCASL.AsUtils
import HasCASL.TypeAna
import HasCASL.DataAna
import HasCASL.VarDecl
import HasCASL.MinType
import HasCASL.TypeCheck

idsToTypePatterns :: [Maybe (Id, [TypeArg])] -> [TypePattern]
idsToTypePatterns mis = map ( \ (i, as) -> TypePattern i as [] ) 
                         $ catMaybes mis

anaFormula :: GlobalAnnos -> Annoted Term -> State Env (Maybe (Annoted Term))
anaFormula ga at = 
    do mt <- resolveTerm ga (Just logicalType) $ item at 
       return $ case mt of Nothing -> Nothing
                           Just e -> Just at { item = e }

anaVars :: Vars -> Type -> Result [VarDecl]
anaVars (Var v) t = return [VarDecl v t Other []]
anaVars (VarTuple vs _) t = 
    case unalias t of 
           ProductType ts _ -> 
               if length ts == length vs then 
                  let lrs = zipWith anaVars vs ts 
                      lms = map maybeResult lrs in
                      if all isJust lms then 
                         return $ concatMap fromJust lms
                         else Result (concatMap diags lrs) Nothing 
               else mkError "wrong arity" t
           _ -> mkError "product type expected" t

mapAnMaybe :: (Monad m) => (a -> m (Maybe b)) -> [Annoted a] -> m [Annoted b]
mapAnMaybe f al = 
    do il <- mapAnM f al
       return $ map ( \ a -> replaceAnnoted (fromJust $ item a) a) $ 
              filter (isJust . item) il 

anaTypeItems :: GlobalAnnos -> GenKind -> Instance -> [Annoted TypeItem] 
            -> State Env [Annoted TypeItem]
anaTypeItems ga gk inst l = do
    ul <- mapAnMaybe ana1TypeItem l
    let tys = map ( \ (Datatype d) -> dataPatToType d) $ 
              filter ( \ t -> case t of 
                       Datatype _ -> True
                       _ -> False) $ map item ul
    rl <- mapAnMaybe (anaTypeItem ga gk inst tys) ul
    addDataSen tys
    return rl

addDataSen :: [DataPat] -> State Env ()
addDataSen tys = do 
    tm <- gets typeMap
    let tis = map ( \ (i, _, _) -> i) tys
        ds = foldr ( \ i dl -> case Map.lookup i tm of 
                     Nothing -> dl
                     Just ti -> case typeDefn ti of
                                DatatypeDefn dd -> dd : dl
                                _ -> dl) [] tis
        sen = NamedSen ("ga_" ++ showSepList (showString "_") showId tis "") 
              $ DatatypeSen ds
    if null tys then return () else appendSentences [sen]

ana1TypeItem :: TypeItem -> State Env (Maybe TypeItem)
ana1TypeItem (Datatype d) = 
    do md <- ana1Datatype d
       return $ fmap Datatype md
ana1TypeItem t = return $ Just t 

-- | analyse a 'TypeItem'
anaTypeItem :: GlobalAnnos -> GenKind -> Instance -> [DataPat] -> TypeItem 
            -> State Env (Maybe TypeItem)
anaTypeItem _ _ inst _ (TypeDecl pats kind ps) = 
    do ak <- anaKind kind
       let Result ds (Just is) = convertTypePatterns pats
       addDiags ds
       mis <- mapM (addTypePattern NoTypeDefn inst ak) is
       return $ if null mis then Nothing else 
              Just $ TypeDecl (idsToTypePatterns mis) ak ps

anaTypeItem _ _ inst _ (SubtypeDecl pats t ps) = 
    do let Result ds (Just is) = convertTypePatterns pats
       addDiags ds  
       tm <- gets typeMap
       let Result _ mp = anaType (Nothing, t) tm
       case mp of 
           Nothing -> do 
               mis <- mapM (addTypePattern NoTypeDefn inst star) is
               let newPats = idsToTypePatterns mis
               mt <- anaStarType t
               case mt of
                   Nothing -> return $ Just $ TypeDecl newPats star ps
                   Just newT -> do mapM_ (addSuperType newT) $ map fst is
                                   return $ Just $ SubtypeDecl newPats newT ps
           Just (ak, newT) -> do 
              mis <- mapM (addTypePattern NoTypeDefn inst ak) is
              let newPats = idsToTypePatterns mis
              mapM_ (addSuperType newT) $ map fst is   
              return $ Just $ SubtypeDecl newPats newT ps

anaTypeItem _ _ inst _ (IsoDecl pats ps) = 
    do let Result ds (Just is) = convertTypePatterns pats
           js = map fst is
       addDiags ds
       mis <- mapM (addTypePattern NoTypeDefn inst star) is
       mapM_ ( \ i -> mapM_ (addSuperType (TypeName i star 0)) js) js 
       return $ if null mis then Nothing else 
              Just $ IsoDecl (idsToTypePatterns mis) ps

anaTypeItem ga _ inst _ (SubtypeDefn pat v t f ps) = 
    do let Result ds m = convertTypePattern pat
       addDiags ds
       case m of 
           Nothing -> return Nothing
           Just (i, as) -> do 
               tm <- gets typeMap
               newAs <- mapM anaTypeVarDecl as 
               mt <- anaStarType t
               let nAs = catMaybes newAs
                   newPat = TypePattern i nAs []
               case mt of 
                   Nothing -> return Nothing
                   Just ty -> do
                       newPty <- generalizeS $ TypeScheme nAs ty []
                       let fullKind = typeArgsListToKind nAs star
                           Result es mvds = anaVars v $ monoType ty
                           altDecl = Just $ AliasType newPat (Just fullKind)
                                     newPty ps
                           altAct = addTypeId True (AliasTypeDefn newPty) inst 
                                    fullKind i >> return altDecl
                       addDiags es
                       if cyclicType i ty then do 
                           addDiags [mkDiag Error 
                                     "illegal recursive subtype definition" ty]
                           return Nothing
                           else case mvds of 
                           Nothing -> altAct
                           Just vds -> do 
                               checkUniqueVars vds
                               vs <- gets localVars
                               mapM_ addLocalVar vds
                               mf <- anaFormula ga f
                               putTypeMap tm
                               putLocalVars vs
                               case mf of 
                                   Nothing -> altAct
                                   Just newF -> do 
                                       addTypeId True (Supertype v newPty
                                                      $ item newF)
                                           inst fullKind i
                                       addSuperType ty i
                                       return $ Just $ SubtypeDefn newPat v ty 
                                              newF ps

anaTypeItem _ _ inst _ (AliasType pat mk sc ps) = 
    do let Result ds m = convertTypePattern pat
       addDiags ds
       case m of 
              Nothing -> return Nothing
              Just (i, as) -> do
                  tm <- gets typeMap
                  newAs <- mapM anaTypeVarDecl as 
                  (ik, mt) <- anaPseudoType mk sc
                  putTypeMap tm
                  let nAs = catMaybes newAs
                  case mt of 
                          Nothing -> return Nothing
                          Just (TypeScheme args ty qs) -> 
                              if cyclicType i ty then 
                                do addDiags [mkDiag Error 
                                       "illegal recursive type synonym" ty]
                                   return Nothing
                                else do 
                                let allArgs = nAs++args
                                    fullKind = typeArgsListToKind nAs ik
                                    allSc = TypeScheme allArgs ty qs
                                newPty <- generalizeS allSc
                                addTypeId True (AliasTypeDefn newPty) 
                                        inst fullKind i 
                                return $ Just $ AliasType (TypePattern i [] [])
                                        (Just fullKind) newPty ps

anaTypeItem _ gk inst tys (Datatype d) = 
    do mD <- anaDatatype gk inst tys d 
       case mD of 
           Nothing -> return Nothing
           Just newD -> return $ Just $ Datatype newD

ana1Datatype :: DatatypeDecl -> State Env (Maybe DatatypeDecl)
ana1Datatype (DatatypeDecl pat kind alts derivs ps) = 
    do k <- anaKind kind
       addDiags $ checkKinds pat star k
       cm <- gets classMap
       let rms = map ( \ c -> anaClassId c cm) derivs
           jcs = catMaybes $ map maybeResult rms
           newDerivs = foldr( \ ck l -> case ck of 
                                           ClassKind ci _ -> ci:l
                                           _ -> l) [] jcs
           Result ds m = convertTypePattern pat
       addDiags (ds ++ concatMap diags rms) 
       addDiags $ concatMap (checkKinds pat star) jcs
       case m of 
              Nothing -> return Nothing
              Just (i, as) -> do 
                  tm <- gets typeMap
                  newAs <- mapM anaTypeVarDecl as
                  putTypeMap tm
                  let nAs = catMaybes newAs
                      fullKind = typeArgsListToKind nAs k
                  addDiags $ checkUniqueTypevars nAs
                  mi <- addTypeId False PreDatatype Plain fullKind i 
                  return $ case mi of 
                          Nothing -> Nothing 
                          Just _ -> Just $ DatatypeDecl (TypePattern i nAs []) 
                                    k alts newDerivs ps

dataPatToType :: DatatypeDecl -> DataPat
dataPatToType (DatatypeDecl (TypePattern i nAs _) k _ _ _) =
     (i, nAs, k)
dataPatToType _ = error "dataPatToType"

-- | add a supertype to a given type id
addSuperType :: Type -> Id -> State Env ()
addSuperType t i =
    do tm <- gets typeMap
       case Map.lookup i tm of
           Nothing -> return () -- previous error
           Just ti@(TypeInfo ok ks sups defn) -> 
               if isTypeVarDefn ti then
                  addDiags[mkDiag Error "illegal supertype for variable" t]
               else if any (== t) sups then 
                  addDiags[mkDiag Hint "repeated supertype" t]
               else putTypeMap $ Map.insert i 
                        (TypeInfo ok ks (t:sups) defn) tm

addDataSubtype :: DataPat -> Type -> State Env ()
addDataSubtype dt st = 
    case st of 
    TypeName i _ _ -> addSuperType (typeIdToType dt) i 
    _ -> addDiags [mkDiag Warning "data subtype ignored" st]

-- | analyse a 'DatatypeDecl'
anaDatatype :: GenKind -> Instance -> [DataPat] 
            -> DatatypeDecl -> State Env (Maybe DatatypeDecl)
anaDatatype genKind inst tys
       d@(DatatypeDecl (TypePattern i nAs _) k alts _ _) = 
    do let dt = dataPatToType d
           fullKind = typeArgsListToKind nAs k
       tm <- gets typeMap
       mapM_ (addTypeVarDecl False) nAs
       mNewAlts <- fromResult (anaAlts tys dt (map item alts) . typeMap)
       putTypeMap tm
       case mNewAlts of 
         Nothing -> return Nothing
         Just newAlts -> do 
           mapM_ (addDataSubtype dt) $ foldr 
             ( \ (Construct mc ts _ _) l -> case mc of
               Nothing -> ts ++ l
               Just _ -> l) [] newAlts
           mapM_ ( \ (Construct mc tc p sels) -> case mc of 
               Nothing -> return ()
               Just c -> do
                   let ty = TypeScheme nAs (getConstrType dt p tc) []
                   sc <- generalizeS ty 
                   addOpId c sc [] (ConstructData i) 
                   mapM_ ( \ (Select ms ts pa) -> case ms of 
                           Just s -> addOpId s (getSelType dt pa ts) []
                                       $ SelectData [ConstrInfo c sc] i
                           Nothing -> return Nothing) $ concat sels) newAlts
           let de = DataEntry Map.empty i genKind nAs newAlts
           addTypeId True (DatatypeDefn de) inst fullKind i
           appendSentences $ makeDataSelEqs de k
           return $ Just d 
anaDatatype _ _ _ _ = error "anaDatatype (not preprocessed)"

-- | analyse a pseudo type (represented as a 'TypeScheme')
anaPseudoType :: Maybe Kind -> TypeScheme -> State Env (Kind, Maybe TypeScheme)
anaPseudoType mk (TypeScheme tArgs ty p) =
    do k <- case mk of 
            Nothing -> return Nothing
            Just j -> fromResult $ anaKindM j
       tm <- gets typeMap    -- save global variables  
       mapM_ anaTypeVarDecl tArgs
       mp <- fromResult (anaType (k, ty) . typeMap)
       putTypeMap tm       -- forget local variables 
       case mp of
           Nothing -> return (star, Nothing)
           Just (sk, newTy) -> do 
              let newK = typeArgsListToKind tArgs sk
              case k of 
                     Nothing -> return () 
                     Just j -> addDiags $ checkKinds ty j newK
              return (newK, Just $ TypeScheme tArgs newTy p)

-- | add a type pattern 
addTypePattern :: TypeDefn -> Instance -> Kind -> (Id, [TypeArg])  
               -> State Env (Maybe (Id, [TypeArg]))

addTypePattern defn inst kind (i, as) =
    do tm <- gets typeMap
       newAs <- mapM anaTypeVarDecl as 
       let nAs = catMaybes newAs
           fullKind = typeArgsListToKind nAs kind
       putTypeMap tm
       addDiags $ checkUniqueTypevars nAs
       mId <- addTypeId True defn inst fullKind i
       return $ case mId of 
                Nothing -> Nothing
                Just newId -> Just (newId, nAs)

-- | convert type patterns
convertTypePatterns :: [TypePattern] -> Result [(Id, [TypeArg])]
convertTypePatterns [] = Result [] $ Just []
convertTypePatterns (s:r) =
    let Result d m = convertTypePattern s
        Result ds (Just l) = convertTypePatterns r
        in case m of 
                  Nothing -> Result (d++ds) $ Just l
                  Just i -> Result (d++ds) $ Just (i:l)

illegalTypePattern, illegalTypePatternArg, illegalTypeId 
    :: TypePattern -> Result a 
illegalTypePattern tp = mkError "illegal type pattern" tp
illegalTypePatternArg tp = mkError "illegal type pattern argument" tp
illegalTypeId tp = mkError "illegal type pattern identifier" tp

-- | convert a 'TypePattern'
convertTypePattern :: TypePattern -> Result (Id, [TypeArg])
convertTypePattern (TypePattern t as _) = return (t, as)
convertTypePattern tp@(TypePatternToken t) = 
    if isPlace t then illegalTypePattern tp
       else return (simpleIdToId t, []) 
convertTypePattern tp@(MixfixTypePattern 
                       [ra, ri@(TypePatternToken inTok), rb]) =
    if head (tokStr inTok) `elem` signChars
       then let inId = Id [Token place $ getMyPos ra, inTok, 
                           Token place $ getMyPos rb] [] [] in
       case (ra, rb) of 
            (TypePatternToken (Token "__" _),
             TypePatternToken (Token "__" _)) -> return (inId, [])
            _ -> do a <- convertToTypeArg ra
                    b <- convertToTypeArg rb
                    return (inId, [a, b])
    else case ra of 
         TypePatternToken t1 -> do 
             a <- convertToTypeArg ri
             b <- convertToTypeArg rb
             return (simpleIdToId t1, [a, b])
         _ -> illegalTypePattern tp
convertTypePattern tp@(MixfixTypePattern (TypePatternToken t1 : rp)) =
    if isPlace t1 then 
       case rp of 
               [TypePatternToken inId, TypePatternToken t2] -> 
                   if isPlace t2 && head (tokStr inId) `elem` signChars
                     then return (Id [t1,inId,t2] [] [], [])
                   else illegalTypePattern tp
               _ -> illegalTypePattern tp
    else case rp of
         [BracketTypePattern Squares as@(_:_) ps] -> do 
             is <- mapM convertToId as 
             return (Id [t1] is ps, [])
         _ -> do as <- mapM convertToTypeArg rp 
                 return (simpleIdToId t1, as)
convertTypePattern (BracketTypePattern bk [ap] ps) =
    case bk of 
    Parens -> convertTypePattern ap
    _ -> let (o, c) = getBrackets bk
             tid = Id [Token o $ head ps, Token place $ getMyPos ap, 
                       Token c $ last ps] [] [] in  
         case ap of 
         TypePatternToken t -> if isPlace t then 
             return (tid, [])
             else return (tid, [TypeArg (simpleIdToId t) MissingKind Other []])
         _ -> do a <- convertToTypeArg ap
                 return (tid, [a])
convertTypePattern tp = illegalTypePattern tp

convertToTypeArg :: TypePattern -> Result TypeArg
convertToTypeArg tp@(TypePatternToken t) = 
    if isPlace t then illegalTypePatternArg tp
    else return $ TypeArg (simpleIdToId t) MissingKind Other []
convertToTypeArg (TypePatternArg a _) =  return a
convertToTypeArg (BracketTypePattern Parens [tp] _) =  convertToTypeArg tp
convertToTypeArg tp = illegalTypePatternArg tp

convertToId :: TypePattern -> Result Id
convertToId tp@(TypePatternToken t) = 
    if isPlace t then illegalTypeId tp
       else return $ Id [t] [] []
convertToId (MixfixTypePattern []) = error "convertToId: MixfixTypePattern []"
convertToId (MixfixTypePattern (hd:tps)) = 
         if null tps then convertToId hd
         else do 
         let (toks, comps) = break ( \ p -> 
                        case p of BracketTypePattern Squares (_:_) _ -> True
                                  _ -> False) tps
         ts <- mapM convertToToks (hd:toks)
         (is, ps) <- if null comps then return ([], []) 
                     else convertToIds $ head comps
         pls <- if null comps then return [] 
                else mapM convertToPlace $ tail comps
         return $ Id (concat ts ++ pls) is ps
convertToId tp = do 
    ts <- convertToToks tp
    return $ Id ts [] []

convertToIds :: TypePattern -> Result ([Id], [Pos])
convertToIds (BracketTypePattern Squares tps@(_:_) ps) = do
    is <- mapM convertToId tps
    return (is, ps)
convertToIds tp = illegalTypeId tp

convertToToks :: TypePattern -> Result [Token]
convertToToks (TypePatternToken t) = return [t]
convertToToks (BracketTypePattern bk [tp] ps) = case bk of 
    Parens -> illegalTypeId tp 
    _ -> do let [o,c] = mkBracketToken bk ps
            ts <- convertToToks tp 
            return (o : ts ++ [c])
convertToToks(MixfixTypePattern tps) = do
    ts <- mapM convertToToks tps
    return $ concat ts
convertToToks tp = illegalTypeId tp

convertToPlace :: TypePattern -> Result Token
convertToPlace tp@(TypePatternToken t) = 
    if isPlace t then return t
       else illegalTypeId tp
convertToPlace tp = illegalTypeId tp
