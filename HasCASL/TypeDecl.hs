
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
import qualified Common.Lib.Map as Map
import Common.Id
import HasCASL.Le
import HasCASL.Reader
import Data.Maybe
import Common.Lib.State

import Common.Lib.Parsec
import Common.Lib.Parsec.Error

import Common.Result
import Common.PrettyPrint
import HasCASL.TypeAna

compatibleTypeDefn :: TypeDefn -> TypeDefn -> Id -> [Diagnosis]
compatibleTypeDefn d1 d2 i = 
    if case (d1, d2) of 
	    (TypeVarDefn, TypeVarDefn) -> True
	    (TypeVarDefn, _) -> False
	    (_, TypeVarDefn) -> False
	    _ -> True
    then [] else [mkDiag Error "incompatible redeclaration of type" i]

addTypeKind :: TypeDefn -> Id -> Kind -> State Env ()
addTypeKind d i k = 
    if isPrefix i then do addSingleTypeKind d i k
			  addSingleTypeKind d (stripFinalPlaces i) k
    else addSingleTypeKind d i k

addSingleTypeKind :: TypeDefn -> Id -> Kind -> State Env ()
addSingleTypeKind d i k = 
    do tk <- gets typeMap
       case Map.lookup i tk of
	      Nothing -> putTypeMap $ Map.insert i 
			 (TypeInfo k [] [] d) tk
	      Just (TypeInfo ok ks sups defn) -> 
		  do cMap <- gets classMap
		     appendDiags $ checkKinds cMap (posOfId i) k ok
		     if any (==k) (ok:ks)
			then addDiag $ mkDiag Warning 
				 "redeclared type" i
				 else putTypeMap $ Map.insert i 
					 (TypeInfo ok
					       (k:ks) sups defn) tk

addSuperType :: Type -> Id -> State Env ()
addSuperType t i =
    do tk <- gets typeMap
       case Map.lookup i tk of
	      Nothing -> return () -- previous error
	      Just (TypeInfo ok ks sups defn) -> 
				putTypeMap $ Map.insert i 
					      (TypeInfo ok ks (t:sups) defn)
					      tk

anaTypeItem :: GenKind -> Instance -> TypeItem -> State Env ()
anaTypeItem _ inst (TypeDecl pats kind _) = 
    do Result es (Just k) <- toState classMap $ anaKind kind
       let Result ds (Just is) = convertTypePatterns pats
       appendDiags (es++ds)
       mapM_ (anaTypeId NoTypeDefn inst kind) is   
anaTypeItem _ inst (SubtypeDecl pats t _) = 
    do sup <- anaType t
       let Result ds (Just is) = convertTypePatterns pats
       appendDiags ds
       mapM_ (anaTypeId NoTypeDefn inst star) is   
       mapM_ (addSuperType t) is

anaTypeItem _ inst (IsoDecl pats _) = 
    do let Result ds (Just is) = convertTypePatterns pats
       appendDiags ds
       mapM_ (anaTypeId NoTypeDefn inst star) is
       mapM_ ( \ i -> mapM_ (addSuperType (TypeName i star 0)) is) is 

anaTypeItem _ inst (SubtypeDefn pat v t f ps) = 
    do (mk, newT) <- anaType t
       k <- case mk of 
	      Nothing -> return star
	      Just k -> do cMap <- gets classMap
			   appendDiags $ checkKinds cMap (posOfType t) k star 
			   return k
       addDiag $ Diag Warning ("unchecked formula '" ++ showPretty f "'")
		   $ firstPos [v] ps
       let Result ds m = convertTypePattern pat
       appendDiags ds
       case m of 
	      Nothing -> return ()
	      Just i -> do anaTypeId (Supertype v newT $ item f) 
				     inst k i
			   addSuperType newT i
	   
anaTypeItem _ inst (AliasType pat mk sc _) = 
    do (ik, newPty) <- anaPseudoType mk sc
       let Result ds m = convertTypePattern pat
       appendDiags ds
       case (m, ik) of 
	      (Just i, Just ki) -> anaTypeId (AliasTypeDefn newPty) inst ki i 
	      _ -> return ()

anaTypeItem gk inst (Datatype d) = anaDatatype gk inst d 

anaDatatype :: GenKind -> Instance -> DatatypeDecl -> State Env ()
anaDatatype genKind inst (DatatypeDecl pat kind _alts derivs ps) =
    do Result es (Just k) <- toState classMap $ anaKind kind
       cMap <- gets classMap
       appendDiags $ checkKinds cMap (firstPos [pat] ps) k star
       case derivs of 
		   Just c -> 
		       do Result cs (Just (dk, _)) <- toState classMap 
						      $ anaClass c
			  appendDiags (cs ++ checkKinds cMap 
						(posOfClass c) dk star)
		   Nothing -> return ()
       let Result ds m = convertTypePattern pat
       appendDiags (es++ds)
       case m of 
	      Nothing -> return ()
	      Just i -> 
		  do -- newAlts <- anaAlts i alts 
		     anaTypeId (DatatypeDefn genKind []) inst k i 

-- TO DO analyse alternatives and add them to Datatype Defn
-- anaAlts :: Id -> 

anaPseudoType :: Maybe Kind -> TypeScheme -> State Env (Maybe Kind, TypeScheme)
anaPseudoType mk (TypeScheme tArgs (q :=> ty) p) =
    do k <- case mk of 
	    Nothing -> return Nothing
	    Just j -> fmap maybeResult $ toState classMap $ anaKind j
       tm <- gets typeMap    -- save global variables  
       mapM_ anaTypeVarDecl tArgs
       (ik, newTy) <- anaType ty
       let newPty = TypeScheme tArgs (q :=> newTy) p
       sik <- case ik of
	      Nothing -> return k
	      Just sk -> do let newK = typeArgsListToKind tArgs sk
			    case k of 
			        Nothing -> return ()
			        Just ki -> do cMap <- gets classMap 
					      appendDiags $ checkKinds cMap 
						      (posOfType ty) ki newK
			    return $ Just newK
       putTypeMap tm       -- forget local variables 
       return (sik, newPty)

typeArgsListToKind :: [TypeArg] -> Kind -> Kind
typeArgsListToKind tArgs k = 
    if null tArgs then k
       else typeArgsListToKind (init tArgs) 
	    (KindAppl (typeArgToKind $ last tArgs) k []) 

typeArgToKind :: TypeArg -> Kind
typeArgToKind (TypeArg _ k _ _) = k

anaTypeVarDecl :: TypeArg -> State Env ()
anaTypeVarDecl(TypeArg t k _ _) = 
    do Result ds (Just nk) <- toState classMap $ anaKind k
       addTypeKind TypeVarDefn t nk

kindArity :: ApplMode -> Kind -> Int
kindArity m (KindAppl k1 k2 _) =
    case m of 
	       TopLevel -> kindArity OnlyArg k1 + 
			   kindArity TopLevel k2
	       OnlyArg -> 1
kindArity m (ExtClass _ _ _) = case m of
			     TopLevel -> 0
			     OnlyArg -> 1

anaTypeId :: TypeDefn -> Instance -> Kind -> Id -> State Env ()
-- type args not yet considered for kind construction 
anaTypeId defn _ kind i@(Id ts _ _)  = 
    do cMap <- gets classMap
       let n = length $ filter isPlace ts 
           nk = expandKind cMap kind
       if n <= kindArity TopLevel nk then
	  addTypeKind defn i kind
	  else addDiag $ mkDiag Error "wrong arity of" i

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
