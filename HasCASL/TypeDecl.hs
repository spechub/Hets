{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2003
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable (MonadState)
    
analyse type decls

-}

module HasCASL.TypeDecl where

import HasCASL.As
import HasCASL.AsUtils
import Common.AS_Annotation
import HasCASL.ClassAna
import qualified Common.Lib.Map as Map
import Common.Id
import HasCASL.Le
import Data.Maybe
import Data.List
import Common.Lib.State

import Common.Lib.Parsec
import Common.Lib.Parsec.Error

import Common.Result
import Common.PrettyPrint
import HasCASL.ClassAna
import HasCASL.TypeAna
import HasCASL.DataAna
import HasCASL.Unify
import HasCASL.Merge

-- ---------------------------------------------------------------------------
-- storing type ids with their kind and definition
-- ---------------------------------------------------------------------------

-- | store a complete type map
putTypeMap :: TypeMap -> State Env ()
putTypeMap tk =  do { e <- get; put e { typeMap = tk } }

-- | store type id and check the kind
addTypeId :: TypeDefn -> Instance -> Kind -> Id -> State Env ()
-- type args not yet considered for kind construction 
addTypeId defn _ kind i = 
    do nk <- expandKind kind
       if placeCount i <= kindArity TopLevel nk then
	  addTypeKind defn i kind
	  else addDiags [mkDiag Error "wrong arity of" i]

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

-- ---------------------------------------------------------------------------
-- analyse type items
-- ---------------------------------------------------------------------------

anaTypeItem :: GenKind -> Instance -> TypeItem -> State Env ()
anaTypeItem _ inst (TypeDecl pats kind _) = 
    do anaKind kind
       let Result ds (Just is) = convertTypePatterns pats
       addDiags ds
       mapM_ (addTypeId NoTypeDefn inst kind) is   
anaTypeItem _ inst (SubtypeDecl pats t _) = 
    do let Result ds (Just is) = convertTypePatterns pats
       addDiags ds  
       mapM_ (addTypeId NoTypeDefn inst star) is   
       mt <- anaStarType t
       case mt of
           Nothing -> return ()
           Just newT -> mapM_ (addSuperType newT) is

anaTypeItem _ inst (IsoDecl pats _) = 
    do let Result ds (Just is) = convertTypePatterns pats
       addDiags ds
       mapM_ (addTypeId NoTypeDefn inst star) is
       mapM_ ( \ i -> mapM_ (addSuperType (TypeName i star 0)) is) is 

anaTypeItem _ inst (SubtypeDefn pat v t f ps) = 
    do addDiags [Diag Warning ("unchecked formula '" ++ showPretty f "'")
		$ firstPos [v] ps]
       let Result ds m = convertTypePattern pat
       addDiags ds
       mt <- anaStarType t
       case m of 
	      Nothing -> return ()
	      Just i -> case mt of 
		  Nothing -> return ()
		  Just newT -> do 		  
		      addTypeId (Supertype v newT $ item f) inst star i
		      addSuperType newT i
       addDiags [Diag Warning ("unchecked formula '" ++ showPretty f "'")
		   $ firstPos [v] ps]
				   
	   
anaTypeItem _ inst (AliasType pat mk sc _) = 
    do let Result ds m = convertTypePattern pat
       addDiags ds
       (ik, mt) <- anaPseudoType mk sc
       case m of 
	      Just i -> case mt of 
		  Nothing -> return ()
		  Just newPty -> addTypeId (AliasTypeDefn newPty) inst ik i 
	      _ -> return ()

anaTypeItem gk inst (Datatype d) = anaDatatype gk inst d 

anaDatatype :: GenKind -> Instance -> DatatypeDecl -> State Env ()
anaDatatype genKind inst (DatatypeDecl pat kind alts derivs _) =
    do k <- anaKind kind
       checkKinds pat star k
       case derivs of 
		   Just c -> do (dk, _) <- anaClass c
				checkKinds c star dk
		   Nothing -> return ()
       let Result ds m = convertTypePattern pat
       addDiags ds
       case m of 
	      Nothing -> return ()
	      Just i -> 
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
		     addTypeId (DatatypeDefn genKind [] newAlts) inst k i 

anaPseudoType :: Maybe Kind -> TypeScheme -> State Env (Kind, Maybe TypeScheme)
anaPseudoType mk (TypeScheme tArgs (q :=> ty) p) =
    do k <- case mk of 
	    Nothing -> return star
	    Just j -> anaKind j
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

typeArgsListToKind :: [TypeArg] -> Kind -> Kind
typeArgsListToKind tArgs k = 
    if null tArgs then k
       else typeArgsListToKind (init tArgs) 
	    (KindAppl (typeArgToKind $ last tArgs) k []) 

typeArgToKind :: TypeArg -> Kind
typeArgToKind (TypeArg _ k _ _) = k

anaTypeVarDecl :: TypeArg -> State Env ()
anaTypeVarDecl(TypeArg t k _ _) = 
    do nk <- anaKind k
       addTypeId TypeVarDefn Plain nk t

kindArity :: ApplMode -> Kind -> Int
kindArity m (KindAppl k1 k2 _) =
    case m of 
	       TopLevel -> kindArity OnlyArg k1 + 
			   kindArity TopLevel k2
	       OnlyArg -> 1
kindArity m (ExtClass _ _ _) = case m of
			     TopLevel -> 0
			     OnlyArg -> 1

convertTypePatterns :: [TypePattern] -> Result [Id]
convertTypePatterns [] = Result [] $ Just []
convertTypePatterns (s:r) =
    let Result d m = convertTypePattern s
	Result ds (Just l) = convertTypePatterns r
	in case m of 
		  Nothing -> Result (d++ds) $ Just l
		  Just i -> Result (d++ds) $ Just (i:l)

convertTypePattern, makeMixTypeId :: TypePattern -> Result Id
convertTypePattern (TypePattern t _ _) = return t
convertTypePattern(TypePatternToken t) = 
    if isPlace t then fatal_error ("illegal type '__'") (tokPos t)
       else return $ (simpleIdToId t)

convertTypePattern t =
    if {- hasPlaces t && -} hasTypeArgs t then
       fatal_error ( "arguments in type patterns not yet supported")
		   -- "illegal mix of '__' and '(...)'"  
                   (posOfTypePattern t)
    else makeMixTypeId t

-- trailing places are not necessary for curried kinds
-- and will be ignored to avoid different Ids "Pred" and "Pred__"

typePatternToTokens :: TypePattern -> [Token]
typePatternToTokens (TypePattern ti _ _) = getPlainTokenList ti
typePatternToTokens (TypePatternToken t) = [t]
typePatternToTokens (MixfixTypePattern ts) = concatMap typePatternToTokens ts
typePatternToTokens (BracketTypePattern pk ts ps) =
    let tts = map typePatternToTokens ts 
	expanded = concat $ expandPos (:[]) (getBrackets pk) tts ps in
	case (pk, tts) of 
		(Parens, [t@[_]]) -> t
		_ -> expanded
typePatternToTokens (TypePatternArg (TypeArg v _ _ _) _) =
    [Token "__" (posOfId v)]

-- compound Ids not supported yet
getToken :: GenParser Token st Token
getToken = token tokStr tokPos Just

parseTypePatternId :: GenParser Token st Id
parseTypePatternId =
    do ts <- many1 getToken 
       return $ Id ts [] []

makeMixTypeId t = 
    case parse parseTypePatternId "" (typePatternToTokens t) of
    Left err -> fatal_error (showErrorMessages "or" "unknown parse error" 
                             "expecting" "unexpected" "end of input"
			     (errorMessages err)) 
		(errorPos err)
    Right x -> return x

hasPlaces, hasTypeArgs :: TypePattern -> Bool
hasPlaces (TypePattern _ _ _) = False
hasPlaces (TypePatternToken t) = isPlace t
hasPlaces (MixfixTypePattern ts) = any hasPlaces ts
hasPlaces (BracketTypePattern _ ts _) = any hasPlaces ts
hasPlaces (TypePatternArg _ _) = False

hasTypeArgs (TypePattern _ _ _) = True
hasTypeArgs (TypePatternToken _) = False
hasTypeArgs (MixfixTypePattern ts) = any hasTypeArgs ts
hasTypeArgs (BracketTypePattern _ ts _) = any hasTypeArgs ts
hasTypeArgs (TypePatternArg _ _) = True

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
addOpId :: UninstOpId -> TypeScheme -> [OpAttr] -> OpDefn -> State Env () 
addOpId i sc attrs defn = 
    do as <- gets assumps
       tm <- gets typeMap
       c <- gets counter
       let (l,r) = partitionOpId as tm c i sc
	   oInfo = OpInfo sc attrs defn 
       if null l then putAssumps $ Map.insert i 
			 (OpInfos (oInfo : r )) as
	  else do let Result ds mo = merge (head l) oInfo
		  addDiags $ map (improveDiag i) ds
		  case mo of 
		      Nothing -> return ()
		      Just oi -> putAssumps $ Map.insert i 
				 (OpInfos (oi : r )) as
