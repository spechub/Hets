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

import HasCASL.As
import HasCASL.Le
import HasCASL.ClassAna
import HasCASL.Unify
import qualified Common.Lib.Map as Map
import Common.Lexer
import Common.Id
import Common.AS_Annotation
import Common.Lib.State
import Data.Maybe
import Data.List

import Common.Result
import Common.GlobalAnnotations
import HasCASL.ClassAna
import HasCASL.TypeAna
import HasCASL.DataAna
import HasCASL.VarDecl
import HasCASL.TypeCheck

-- | add a supertype to a given type id
addSuperType :: Type -> Id -> State Env ()
addSuperType t i =
    do tk <- gets typeMap
       case Map.lookup i tk of
	      Nothing -> return () -- previous error
	      Just (TypeInfo ok ks sups defn) -> 
				putTypeMap $ Map.insert i 
					      (TypeInfo ok ks (t:sups) defn)
					      tk

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
    case t of 
	   ProductType ts _ -> 
	       if length ts == length vs then 
		  let lrs = zipWith anaVars vs ts 
		      lms = map maybeResult lrs in
		      if all isJust lms then 
			 return $ concatMap fromJust lms
			 else Result (concatMap diags lrs) Nothing 
	       else Result [mkDiag Error "wrong arity" t] Nothing
	   _ -> Result [mkDiag Error "product type expected" t] Nothing


mapAnMaybe :: (Monad m) => (a -> m (Maybe b)) -> [Annoted a] -> m [Annoted b]
mapAnMaybe f al = 
    do il <- mapAnM f al
       return $ map ( \ a -> a { item = fromJust $ item a }) $ 
	      filter (isJust . item) il 

anaTypeItems :: GlobalAnnos -> GenKind -> Instance -> [Annoted TypeItem] 
	    -> State Env [Annoted TypeItem]
anaTypeItems ga gk inst l = do
    ul <- mapAnMaybe ana1TypeItem l
    let tys = map ( \ (Datatype d) -> dataPatToType d) $ 
	      filter ( \ t -> case t of 
		       Datatype _ -> True
		       _ -> False) $ map item ul
    mapAnM (anaTypeItem ga gk inst tys) ul

ana1TypeItem :: TypeItem -> State Env (Maybe TypeItem)
ana1TypeItem (Datatype d) = 
    do md <- ana1Datatype d
       return $ fmap Datatype md
ana1TypeItem t = return $ Just t 

-- | analyse a 'TypeItem'
anaTypeItem :: GlobalAnnos -> GenKind -> Instance -> [(Id, Type)] -> TypeItem 
	    -> State Env TypeItem
anaTypeItem _ _ inst _ (TypeDecl pats kind ps) = 
    do ak <- anaKind kind
       let Result ds (Just is) = convertTypePatterns pats
       addDiags ds
       mis <- mapM (addTypePattern NoTypeDefn inst ak) is
       return $ TypeDecl (idsToTypePatterns mis) ak ps

anaTypeItem _ _ inst _ (SubtypeDecl pats t ps) = 
    do let Result ds (Just is) = convertTypePatterns pats
       addDiags ds  
       mis <- mapM (addTypePattern NoTypeDefn inst star) is 
       let newPats = idsToTypePatterns mis 
       mt <- anaStarType t
       case mt of
           Nothing -> return $ TypeDecl newPats star ps
           Just newT -> do mapM_ (addSuperType newT) $ map fst is
			   return $ SubtypeDecl newPats newT ps

anaTypeItem _ _ inst _ (IsoDecl pats ps) = 
    do let Result ds (Just is) = convertTypePatterns pats
	   js = map fst is
       addDiags ds
       mis <- mapM (addTypePattern NoTypeDefn inst star) is
       mapM_ ( \ i -> mapM_ (addSuperType (TypeName i star 0)) js) js 
       return $ IsoDecl (idsToTypePatterns mis) ps

anaTypeItem ga _ inst _ (SubtypeDefn pat v t f ps) = 
    do let Result ds m = convertTypePattern pat
       addDiags ds
       case m of 
	      Nothing -> return $ SubtypeDefn pat v t f ps
	      Just (i, as) -> do 
	          tm <- gets typeMap
	          newAs <- mapM anaTypeVarDecl as 
                  mt <- anaStarType t
		  let nAs = catMaybes newAs
		      newPat = TypePattern i nAs []
		  case mt of 
			  Nothing -> return $ SubtypeDefn newPat v t f ps
			  Just ty -> do
			      let newPty = TypeScheme nAs ([]:=>ty) []
				  fullKind = typeArgsListToKind nAs star
				  Result es mvds = anaVars v ty 
			      addDiags es
			      checkUniqueTypevars nAs
			      addSuperType ty i
			      if i `occursIn` ty then do 
			         addDiags [mkDiag Error 
				     "illegal recursive subtype definition" ty]
				 return $ SubtypeDefn newPat v ty f ps
				 else case mvds of 
					    Nothing -> return $ SubtypeDefn 
						         newPat v ty f ps
					    Just vds -> do 
						checkUniqueVars vds
						ass <- gets assumps
				                mapM_ addVarDecl vds
						mf <- anaFormula ga f
						putTypeMap tm
						putAssumps ass 
						case mf of 
						    Nothing -> do 
						        addTypeId True 
							  (AliasTypeDefn 
							   newPty) inst 
							  fullKind i
							return $ AliasType
							       newPat 
							       (Just fullKind)
							       newPty ps
						    Just newF -> do 
						        addTypeId True
						          (Supertype v newPty
							  $ item newF)
						           inst fullKind i
							return $ SubtypeDefn 
							       newPat v ty 
							       newF ps
anaTypeItem _ _ inst _ (AliasType pat mk sc ps) = 
    do let Result ds m = convertTypePattern pat
       addDiags ds
       case m of 
	      Nothing -> return $ AliasType pat mk sc ps
	      Just (i, as) -> do
	          tm <- gets typeMap
	          newAs <- mapM anaTypeVarDecl as 
                  (ik, mt) <- anaPseudoType mk sc
		  putTypeMap tm
		  let nAs = catMaybes newAs
		      newPat = TypePattern i nAs []
		  case mt of 
			  Nothing -> return $ AliasType newPat mk sc ps
			  Just (TypeScheme args qty@(_ :=> ty) qs) -> do 
			      let allArgs = nAs++args
                                  newPty = TypeScheme allArgs qty qs
				  fullKind = typeArgsListToKind nAs ik
			      checkUniqueTypevars allArgs
			      if i `occursIn` ty then do 
			         addDiags [mkDiag Error 
					   "illegal recursive type synonym" ty]
				 return Nothing
				 else addTypeId True (AliasTypeDefn newPty) 
				      inst fullKind i 
			      return $ AliasType (TypePattern i [] [])
				     (Just fullKind) newPty ps

anaTypeItem _ gk inst tys (Datatype d) = 
    do newD <- anaDatatype gk inst tys d 
       return $ Datatype newD
		   

ana1Datatype :: DatatypeDecl -> State Env (Maybe DatatypeDecl)
ana1Datatype (DatatypeDecl pat kind alts derivs ps) = 
    do k <- anaKind kind
       checkKinds pat star k
       cs <- mapM anaClassId derivs
       let jcs = catMaybes cs
           newDerivs = foldr( \ ck l -> case ck of 
				           ClassKind ci _ -> ci:l
				           _ -> l) [] jcs
           Result ds m = convertTypePattern pat
       addDiags ds
       mapM_ (checkKinds pat star) jcs
       case m of 
	      Nothing -> return Nothing
	      Just (i, as) -> do 
		  tm <- gets typeMap
	          newAs <- mapM anaTypeVarDecl as
		  putTypeMap tm
		  let nAs = catMaybes newAs
                      fullKind = typeArgsListToKind nAs k
	          checkUniqueTypevars nAs
		  mi <- addTypeId False PreDatatype Plain fullKind i 
		  return $ case mi of 
			  Nothing -> Nothing 
			  Just _ -> Just $ DatatypeDecl (TypePattern i nAs []) 
				    k alts newDerivs ps

dataPatToType :: DatatypeDecl -> (Id, Type)
dataPatToType (DatatypeDecl (TypePattern i nAs _) k _ _ _) = let      
    fullKind = typeArgsListToKind nAs k
    ti = TypeName i fullKind 0
    mkType ty [] = ty
    mkType ty ((TypeArg ai ak _ _): rest) =
	mkType (TypeAppl ty (TypeName ai ak 1)) rest
    in (i, mkType ti nAs)
dataPatToType _ = error "dataPatToType"

-- | analyse a 'DatatypeDecl'
anaDatatype :: GenKind -> Instance -> [(Id, Type)] 
	    -> DatatypeDecl -> State Env DatatypeDecl
anaDatatype genKind inst tys
       d@(DatatypeDecl (TypePattern i nAs _) k alts _ _) = 
    do let dt = snd $ dataPatToType d
	   fullKind = typeArgsListToKind nAs k
       tm <- gets typeMap
       mapM_ (addTypeVarDecl False) nAs
       newAlts <- anaAlts tys dt $ map item alts
       mapM_ ( \ (Construct c tc p sels) -> do
			     let ty = TypeScheme nAs 
			                   ([] :=> getConstrType dt p tc) []
			     addOpId c ty
			                [] (ConstructData i)
			     mapM_ ( \ (Select s ts pa) -> 
				     addOpId s (TypeScheme nAs 
					 ([] :=> getSelType dt pa ts) []) 
				     [] (SelectData [ConstrInfo c ty] i)
			           ) sels) newAlts
       putTypeMap tm
       addTypeId True (DatatypeDefn genKind nAs newAlts) inst fullKind i
       return d 
anaDatatype _ _ _ _ = error "anaDatatype (not preprocessed)"

-- | analyse a pseudo type (represented as a 'TypeScheme')
anaPseudoType :: Maybe Kind -> TypeScheme -> State Env (Kind, Maybe TypeScheme)
anaPseudoType mk (TypeScheme tArgs (q :=> ty) p) =
    do k <- case mk of 
	    Nothing -> return Nothing
	    Just j -> anaKindM j
       tm <- gets typeMap    -- save global variables  
       mapM_ anaTypeVarDecl tArgs
       (sk, mt) <- anaType (k, ty)
       let newK = typeArgsListToKind tArgs sk
       case mk of
           Nothing -> return ()
	   Just j -> checkKinds ty j newK
       putTypeMap tm       -- forget local variables 
       case mt of 
           Nothing -> return (newK, Nothing)
	   Just newTy -> return (newK, Just $ TypeScheme tArgs (q :=> newTy) p)

-- | add a type pattern 
addTypePattern :: TypeDefn -> Instance -> Kind -> (Id, [TypeArg])  
	       -> State Env (Maybe (Id, [TypeArg]))

addTypePattern defn inst kind (i, as) =
    do tm <- gets typeMap
       newAs <- mapM anaTypeVarDecl as 
       let nAs = catMaybes newAs
           fullKind = typeArgsListToKind nAs kind
       putTypeMap tm
       checkUniqueTypevars nAs
       mId <- addTypeId True defn inst fullKind i
       return $ case mId of 
		Nothing -> Nothing
		Just newId -> Just (newId, nAs)

-- | extent a kind to expect further type arguments
typeArgsListToKind :: [TypeArg] -> Kind -> Kind
typeArgsListToKind tArgs k = 
    if null tArgs then k
       else typeArgsListToKind (init tArgs) 
	    (FunKind (( \ (TypeArg _ xk _ _) -> xk) $ last tArgs) k []) 

-- | convert type patterns
convertTypePatterns :: [TypePattern] -> Result [(Id, [TypeArg])]
convertTypePatterns [] = Result [] $ Just []
convertTypePatterns (s:r) =
    let Result d m = convertTypePattern s
	Result ds (Just l) = convertTypePatterns r
	in case m of 
		  Nothing -> Result (d++ds) $ Just l
		  Just i -> Result (d++ds) $ Just (i:l)


illegalTypePattern, illegalTypePatternArg  :: TypePattern -> Result a 
illegalTypePattern tp = fatal_error ("illegal type pattern: " ++ 
				  showPretty tp "") $ getMyPos tp
illegalTypePatternArg tp = fatal_error ("illegal type pattern argument: " ++ 
				  showPretty tp "") $ getMyPos tp

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
    else do as <- mapM convertToTypeArg rp 
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

