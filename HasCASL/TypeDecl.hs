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

idsToTypePatterns :: [Maybe Id] -> [TypePattern]
idsToTypePatterns mis = map ( \ i -> TypePattern i [] [] ) 
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
	   _ -> Result [mkDiag Error "product type expected instead" t] Nothing

-- | analyse a 'TypeItem'
anaTypeItem :: GlobalAnnos -> GenKind -> Instance -> TypeItem 
	    -> State Env TypeItem
anaTypeItem _ _ inst (TypeDecl pats kind ps) = 
    do ak <- anaKind kind
       let Result ds (Just is) = convertTypePatterns pats
       addDiags ds
       mis <- mapM (addTypeId NoTypeDefn inst ak) is
       return $ TypeDecl (idsToTypePatterns mis) ak ps

anaTypeItem _ _ inst (SubtypeDecl pats t ps) = 
    do let Result ds (Just is) = convertTypePatterns pats
       addDiags ds  
       mis <- mapM (addTypeId NoTypeDefn inst star) is 
       let newPats = idsToTypePatterns mis 
       mt <- anaStarType t
       case mt of
           Nothing -> return $ TypeDecl newPats star ps
           Just newT -> do mapM_ (addSuperType newT) is
			   return $ SubtypeDecl newPats newT ps

anaTypeItem _ _ inst (IsoDecl pats ps) = 
    do let Result ds (Just is) = convertTypePatterns pats
       addDiags ds
       mis <- mapM (addTypeId NoTypeDefn inst star) is
       mapM_ ( \ i -> mapM_ (addSuperType (TypeName i star 0)) is) is 
       return $ IsoDecl (idsToTypePatterns mis) ps

anaTypeItem ga _ inst (SubtypeDefn pat v t f ps) = 
    do let Result ds m = convertTypePattern pat
       addDiags ds
       mty <- anaStarType t
       let Result es mvds = case mty of 
				     Nothing -> Result [] Nothing
				     Just ty -> anaVars v ty 
       addDiags es
       as <- gets assumps
       mv <- case mvds of 
		       Nothing -> return Nothing
		       Just vds -> do checkUniqueVars vds
				      mvs <- mapM addVarDecl vds
				      if all isJust mvs then 
					 return $ Just v
					 else return Nothing
       mt <- anaFormula ga f
       putAssumps as
       case m of 
	      Nothing -> return $ TypeDecl [] star ps
	      Just (i, _, _) -> case (mt, mv) of 
		  (Just newF, Just _) -> do 
		      let newT = fromJust mty	       
		      mi <- addTypeId (Supertype v newT $ item newF) 
			    inst star i
		      addSuperType newT i
		      case mi of 
			      Nothing -> return $ TypeDecl [] star ps
			      Just _ -> return $ SubtypeDefn
					(TypePattern i [] []) v newT newF ps 
		  _ -> do mi <- addTypeId NoTypeDefn inst star i
			  return $ TypeDecl (idsToTypePatterns [mi]) star ps
	   
anaTypeItem _ _ inst (AliasType pat mk sc ps) = 
    do let Result ds m = convertTypePattern pat
       addDiags ds
       (ik, mt) <- anaPseudoType mk sc
       case m of 
	      Just (i, _, _) -> case mt of 
		  Nothing -> return $ TypeDecl [] star ps
		  Just nsc -> do let newPty = generalize nsc
				 addTypeId (AliasTypeDefn newPty) inst ik i 
				 return $ AliasType (TypePattern i [] [])
					   (Just ik) newPty ps
	      _ -> return $ TypeDecl [] star ps

anaTypeItem _ gk inst (Datatype d) = 
    do newD <- anaDatatype gk inst d 
       return $ Datatype newD
		   
-- | analyse a 'DatatypeDecl'
anaDatatype :: GenKind -> Instance -> DatatypeDecl -> State Env DatatypeDecl
anaDatatype genKind inst (DatatypeDecl pat kind alts derivs ps) =
    do k <- anaKind kind
       checkKinds pat star k
       cs <- mapM anaClassId derivs
       let jcs = catMaybes cs
       mapM (checkKinds pat star) jcs
       let newDerivs = foldr( \ ck l -> case ck of 
				           ClassKind ci _ -> ci:l
				           _ -> l) [] jcs
           Result ds m = convertTypePattern pat
       addDiags ds
       case m of 
	      Nothing -> return $ DatatypeDecl pat k [] newDerivs ps
	      Just (i, _, _) -> 
		  do let dt = TypeName i k 0
                     newAlts <- anaAlts dt 
				$ map item alts
		     mapM_ ( \ (Construct c tc p sels) -> do
			     let ty = simpleTypeScheme $ getConstrType dt p tc
			     addOpId c ty
			                [] (ConstructData i)
			     mapM_ ( \ (Select s ts pa) -> 
				     addOpId s (simpleTypeScheme $ 
						getSelType dt pa ts) 
				     [] (SelectData [ConstrInfo c ty] i)
			           ) sels) newAlts
		     mi <- addTypeId (DatatypeDefn genKind [] newAlts) inst k i
		     return $ DatatypeDecl (TypePattern i [] []) k 
			    (case mi of Nothing -> [] 
			                Just _ -> alts)
			    newDerivs ps


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

-- | extent a kind to expect further type arguments
typeArgsListToKind :: [TypeArg] -> Kind -> Kind
typeArgsListToKind tArgs k = 
    if null tArgs then k
       else typeArgsListToKind (init tArgs) 
	    (FunKind (( \ (TypeArg _ xk _ _) -> xk) $ last tArgs) k []) 

-- | convert mixfix type patterns to ids
convertTypePatterns :: [TypePattern] -> Result [Id]
convertTypePatterns [] = Result [] $ Just []
convertTypePatterns (s:r) =
    let Result d m = convertTypePattern s
	Result ds (Just l) = convertTypePatterns r
	in case m of 
		  Nothing -> Result (d++ds) $ Just l
		  Just (i, _, _) -> Result (d++ds) $ Just (i:l)


illegalTypePattern, illegalTypePatternArg  :: TypePattern -> Result a 
illegalTypePattern tp = fatal_error ("illegal type pattern: " ++ 
				  showPretty tp "") $ getMyPos tp
illegalTypePatternArg tp = fatal_error ("illegal type pattern argument: " ++ 
				  showPretty tp "") $ getMyPos tp

-- | convert a 'TypePattern'
convertTypePattern :: TypePattern -> Result (Id, [TypeArg], Int)
convertTypePattern (TypePattern t as _) = return (t, as, 0)
convertTypePattern tp@(TypePatternToken t) = 
    if isPlace t then illegalTypePattern tp
       else return (simpleIdToId t, [], 0) 
convertTypePattern tp@(MixfixTypePattern (TypePatternToken t1 : rp)) =
    if isPlace t1 then 
       case rp of 
	       [TypePatternToken inId, TypePatternToken t2] -> 
		   if isPlace t2 && head (tokStr inId) `elem` signChars
		     then return (Id [t1,inId,t2] [] [], [], 2)
		   else illegalTypePattern tp
	       _ -> illegalTypePattern tp
    else do as <- mapM convertToTypeArg rp 
	    return (simpleIdToId t1, as, 0)
convertTypePattern tp@(MixfixTypePattern 
		       [TypePatternArg a _, TypePatternToken inId, rb]) =
    if head (tokStr inId) `elem` signChars
       then do b <- convertToTypeArg rb
	       return (Id [Token place $ getMyPos a, inId, 
			   Token place $ getMyPos rb] [] [], [a, b], 0)
    else illegalTypePattern tp
convertTypePattern (BracketTypePattern bk [ap] ps) =
    case bk of 
    Parens -> convertTypePattern ap
    _ -> let (o, c) = getBrackets bk
	     tid = Id [Token o $ head ps, Token place $ getMyPos ap, 
		       Token c $ last ps] [] [] in  
         case ap of 
	 TypePatternToken t -> if isPlace t then 
	     return (tid, [], 1)
 	     else return (tid, [TypeArg (simpleIdToId t) MissingKind Other []]
			 , 0)
	 _ -> do a <- convertToTypeArg ap
		 return (tid, [a], 0)
convertTypePattern tp = illegalTypePattern tp

convertToTypeArg :: TypePattern -> Result TypeArg
convertToTypeArg tp@(TypePatternToken t) = 
    if isPlace t then illegalTypePatternArg tp
    else return $ TypeArg (simpleIdToId t) MissingKind Other []
convertToTypeArg (TypePatternArg a _) =  return a
convertToTypeArg (BracketTypePattern Parens [tp] _) =  convertToTypeArg tp
convertToTypeArg tp = illegalTypePatternArg tp

