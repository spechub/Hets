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
import HasCASL.VarDecl

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

-- | analyse a 'TypeItem'
anaTypeItem :: GenKind -> Instance -> TypeItem -> State Env TypeItem
anaTypeItem _ inst ti@(TypeDecl pats kind _) = 
    do anaKind kind
       let Result ds (Just is) = convertTypePatterns pats
       addDiags ds
       mapM_ (addTypeId NoTypeDefn inst kind) is
       return ti

anaTypeItem _ inst ti@(SubtypeDecl pats t _) = 
    do let Result ds (Just is) = convertTypePatterns pats
       addDiags ds  
       mapM_ (addTypeId NoTypeDefn inst star) is   
       mt <- anaStarType t
       case mt of
           Nothing -> return ()
           Just newT -> mapM_ (addSuperType newT) is
       return ti

anaTypeItem _ inst ti@(IsoDecl pats _) = 
    do let Result ds (Just is) = convertTypePatterns pats
       addDiags ds
       mapM_ (addTypeId NoTypeDefn inst star) is
       mapM_ ( \ i -> mapM_ (addSuperType (TypeName i star 0)) is) is 
       return ti

anaTypeItem _ inst ti@(SubtypeDefn pat v t f ps) = 
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
       return ti
	   
anaTypeItem _ inst ti@(AliasType pat mk sc _) = 
    do let Result ds m = convertTypePattern pat
       addDiags ds
       (ik, mt) <- anaPseudoType mk sc
       case m of 
	      Just i -> case mt of 
		  Nothing -> return ()
		  Just newPty -> do addTypeId (AliasTypeDefn newPty) inst ik i 
				    return ()
	      _ -> return ()
       return ti

anaTypeItem gk inst (Datatype d) = 
    do anaDatatype gk inst d 
       return $ Datatype d
		   
-- | analyse a 'DatatypeDecl'
anaDatatype :: GenKind -> Instance -> DatatypeDecl -> State Env DatatypeDecl
anaDatatype genKind inst dd@(DatatypeDecl pat kind alts derivs _) =
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
		     return ()
       return dd

-- | analyse a pseudo type (represented as a 'TypeScheme')
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

-- | extent a kind to expect further type arguments
typeArgsListToKind :: [TypeArg] -> Kind -> Kind
typeArgsListToKind tArgs k = 
    if null tArgs then k
       else typeArgsListToKind (init tArgs) 
	    (KindAppl (( \ (TypeArg _ xk _ _) -> xk) $ last tArgs) k []) 

-- | convert mixfix type patterns to ids
convertTypePatterns :: [TypePattern] -> Result [Id]
convertTypePatterns [] = Result [] $ Just []
convertTypePatterns (s:r) =
    let Result d m = convertTypePattern s
	Result ds (Just l) = convertTypePatterns r
	in case m of 
		  Nothing -> Result (d++ds) $ Just l
		  Just i -> Result (d++ds) $ Just (i:l)

-- | convert a 'TypePattern' to a type 'Id' via 'makeMixTypeId'
convertTypePattern :: TypePattern -> Result Id
convertTypePattern (TypePattern t _ _) = return t
convertTypePattern(TypePatternToken t) = 
    if isPlace t then fatal_error ("illegal type '__'") (tokPos t)
       else return $ (simpleIdToId t)

convertTypePattern t =
    if hasTypeArgs t then
       fatal_error ( "arguments in type patterns not yet supported")
                   (posOfTypePattern t)
    else makeMixTypeId t

-- trailing places are not necessary for curried kinds
-- and will be ignored to avoid different Ids "Pred" and "Pred__"

-- | decompose a 'TypePattern' into tokens
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
-- | get the next 'Token' from a token list
getToken :: GenParser Token st Token
getToken = token tokStr tokPos Just

-- | parse a type 'Id' from a token list
parseTypePatternId :: GenParser Token st Id
parseTypePatternId =
    do ts <- many1 getToken 
       return $ Id ts [] []

-- | convert a 'TypePattern' to a type 'Id' via 'typePatternToTokens' 
-- and 'parseTypePatternId' 
makeMixTypeId :: TypePattern -> Result Id
makeMixTypeId t = 
    case parse parseTypePatternId "" (typePatternToTokens t) of
    Left err -> fatal_error (showErrorMessages "or" "unknown parse error" 
                             "expecting" "unexpected" "end of input"
			     (errorMessages err)) 
		(errorPos err)
    Right x -> return x

-- | check for type arguments
hasTypeArgs:: TypePattern -> Bool
hasTypeArgs (TypePattern _ _ _) = True
hasTypeArgs (TypePatternToken _) = False
hasTypeArgs (MixfixTypePattern ts) = any hasTypeArgs ts
hasTypeArgs (BracketTypePattern _ ts _) = any hasTypeArgs ts
hasTypeArgs (TypePatternArg _ _) = True

