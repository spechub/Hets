
{- HetCATS/HasCASL/TypeDecl.hs
   $Id$
   Authors: Christian Maeder
   Year:    2003
   
   analyse type decls
-}

module HasCASL.TypeDecl where

import HasCASL.As
import HasCASL.AsUtils
import Common.AS_Annotation(item)
import HasCASL.ClassAna
import HasCASL.ClassDecl
import qualified Common.Lib.Map as Map
import Common.Id
import HasCASL.Le
import Data.Maybe
import Common.Lib.State

import Common.Lib.Parsec
import Common.Lib.Parsec.Error

import Common.Result
import Common.PrettyPrint
import HasCASL.TypeAna
import HasCASL.DataAna
import HasCASL.Reader
import HasCASL.Unify

-- ---------------------------------------------------------------------------
-- analyse types as state
-- ---------------------------------------------------------------------------

fromReadR :: a -> ReadR (ClassMap, TypeMap) a -> State Env a 
fromReadR a r = toState a ( \ e -> (classMap e, typeMap e)) r

anaTypeS :: (Kind, Type) -> State Env (Kind, Type) 
anaTypeS kt = fromReadR kt $ anaType kt 

-- check with merge
compatibleTypeDefn :: TypeDefn -> TypeDefn -> Id -> [Diagnosis]
compatibleTypeDefn d1 d2 i = 
    if case (d1, d2) of 
	    (TypeVarDefn, TypeVarDefn) -> True
	    (TypeVarDefn, _) -> False
	    (_, TypeVarDefn) -> False
	    _ -> True
    then [] else [mkDiag Error "incompatible redeclaration of type" i]

-- ---------------------------------------------------------------------------
-- storing type ids with their kind and definition
-- ---------------------------------------------------------------------------

-- | store a complete type map
putTypeMap :: TypeMap -> State Env ()
putTypeMap tk =  do { e <- get; put e { typeMap = tk } }

-- | store type id and check the kind
addTypeId :: TypeDefn -> Instance -> Kind -> Id -> State Env ()
-- type args not yet considered for kind construction 
addTypeId defn _ kind i@(Id ts _ _)  = 
    do nk <- toState kind classMap $ expandKind kind
       let n = length $ filter isPlace ts 
       if n <= kindArity TopLevel nk then
	  addTypeKind defn i kind
	  else addDiag $ mkDiag Error "wrong arity of" i

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
		  do checkKindsS i k ok
		     if any (==k) (ok:ks)
			then addDiag $ mkDiag Warning 
				 "redeclared type" i
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
    do anaKindS kind
       let Result ds (Just is) = convertTypePatterns pats
       appendDiags ds
       mapM_ (addTypeId NoTypeDefn inst kind) is   
anaTypeItem _ inst (SubtypeDecl pats t _) = 
    do anaTypeS (star, t)
       let Result ds (Just is) = convertTypePatterns pats
       appendDiags ds
       mapM_ (addTypeId NoTypeDefn inst star) is   
       mapM_ (addSuperType t) is

anaTypeItem _ inst (IsoDecl pats _) = 
    do let Result ds (Just is) = convertTypePatterns pats
       appendDiags ds
       mapM_ (addTypeId NoTypeDefn inst star) is
       mapM_ ( \ i -> mapM_ (addSuperType (TypeName i star 0)) is) is 

anaTypeItem _ inst (SubtypeDefn pat v t f ps) = 
    do (k, newT) <- anaTypeS (star, t)
       checkKindsS t star k
       addDiag $ Diag Warning ("unchecked formula '" ++ showPretty f "'")
		   $ firstPos [v] ps
       let Result ds m = convertTypePattern pat
       appendDiags ds
       case m of 
	      Nothing -> return ()
	      Just i -> do addTypeId (Supertype v newT $ item f) 
				     inst k i
			   addSuperType newT i
	   
anaTypeItem _ inst (AliasType pat mk sc _) = 
    do (ik, newPty) <- anaPseudoType mk sc
       let Result ds m = convertTypePattern pat
       appendDiags ds
       case m of 
	      Just i -> addTypeId (AliasTypeDefn newPty) inst ik i 
	      _ -> return ()

anaTypeItem gk inst (Datatype d) = anaDatatype gk inst d 

anaDatatype :: GenKind -> Instance -> DatatypeDecl -> State Env ()
anaDatatype genKind inst (DatatypeDecl pat kind alts derivs _) =
    do k <- anaKindS kind
       checkKindsS pat star k
       case derivs of 
		   Just c -> do (dk, _) <- anaClassS (star, c)
				checkKindsS c star dk
		   Nothing -> return ()
       let Result ds m = convertTypePattern pat
       appendDiags ds
       case m of 
	      Nothing -> return ()
	      Just i -> 
		  do let dt = TypeName i k 0
                     newAlts <- fromReadR [] $ anaAlts dt 
				$ map item alts
		     mapM_ ( \ (Construct c tc p sels) -> do
			     addOpId c (simpleTypeScheme $ 
					getConstrType dt p tc) 
			                [] (ConstructData i)
			     mapM_ ( \ (Select s ts pa) -> 
				     addOpId s (simpleTypeScheme $ 
						getSelType dt pa ts) 
				     [] (SelectData [c] i)
			           ) sels) newAlts
		     addTypeId (DatatypeDefn genKind [] newAlts) inst k i 

anaPseudoType :: Maybe Kind -> TypeScheme -> State Env (Kind, TypeScheme)
anaPseudoType mk (TypeScheme tArgs (q :=> ty) p) =
    do k <- case mk of 
	    Nothing -> return star
	    Just j -> anaKindS j
       tm <- gets typeMap    -- save global variables  
       mapM_ anaTypeVarDecl tArgs
       (sk, newTy) <- anaTypeS (k, ty)
       let newPty = TypeScheme tArgs (q :=> newTy) p
           newK = typeArgsListToKind tArgs sk
       case mk of 
	      Nothing -> return ()
	      Just j -> checkKindsS ty j newK
       putTypeMap tm       -- forget local variables 
       return (newK, newPty)

typeArgsListToKind :: [TypeArg] -> Kind -> Kind
typeArgsListToKind tArgs k = 
    if null tArgs then k
       else typeArgsListToKind (init tArgs) 
	    (KindAppl (typeArgToKind $ last tArgs) k []) 

typeArgToKind :: TypeArg -> Kind
typeArgToKind (TypeArg _ k _ _) = k

anaTypeVarDecl :: TypeArg -> State Env ()
anaTypeVarDecl(TypeArg t k _ _) = 
    do nk <- anaKindS k
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

-- TODO trailing places are not necessary for curried kinds
-- and should be ignored to avoid different Ids "Pred" and "Pred__"

typePatternToTokens :: TypePattern -> [Token]
typePatternToTokens (TypePattern ti _ _) = getTokenList place ti
typePatternToTokens (TypePatternToken t) = [t]
typePatternToTokens (MixfixTypePattern ts) = concatMap typePatternToTokens ts
typePatternToTokens (BracketTypePattern pk ts ps) =
    let tts = map typePatternToTokens ts 
	expanded = concat $ expandPos (:[]) (getBrackets pk) tts ps in
	case pk of 
		Parens -> if length tts == 1 && 
			  length (head tts) == 1 then head tts
			  else expanded
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

unifiable :: TypeScheme -> TypeScheme -> State Env Bool
unifiable sc1 sc2 =
    do tm <- gets typeMap
       c <- gets counter
       let Result ds mm = evalState (unifIable tm sc1 sc2) c
       appendDiags ds
       return $ isJust mm

-- | storing an operation
addOpId :: UninstOpId -> TypeScheme -> [OpAttr] -> OpDefn -> State Env () 
addOpId i sc attrs defn = 
    do as <- gets assumps
       let l = Map.findWithDefault [] i as
       if sc `elem` map opType l then 
	  addDiag $ mkDiag Warning 
		      "repeated value" i
	  else do bs <- mapM (unifiable sc) $ map opType l
		  if or bs then addDiag $ mkDiag Error
			 "illegal overloading of" i
	             else putAssumps $ Map.insert i 
			      (OpInfo sc attrs defn : l ) as
