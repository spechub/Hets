
{- HetCATS/HasCASL/TypeDecl.hs
   $Id$
   Authors: Christian Maeder
   Year:    2003
   
   analyse type decls
-}

module TypeDecl where

import As
import AsUtils
import ClassAna
import FiniteMap
import Id
import Le
import MonadState

import MixfixParser(getTokenList, expandPos)
import Parsec
import ParsecPos
import ParsecError

import PrintAs()
import Result

addTypeKind :: Id -> Kind -> State Env ()
addTypeKind t k = 
    do tk <- getTypeKinds
       case lookupFM tk t of
            Just ks -> let ds = eqKindDiag k $ head ks in
			  if null ds then 
			     putTypeKinds $ addToFM tk t (k:ks)
			     else appendDiags ds
	    _ -> putTypeKinds $ addToFM tk t [k]

anaTypeItem :: Instance -> TypeItem -> State Env ()
anaTypeItem inst (TypeDecl pats kind _) = 
    do k <- anaKind kind
       mapM_ (anaTypePattern inst k) pats 

anaTypeItem _ (SubtypeDecl _ t p) = missingAna t p
anaTypeItem _ t@(IsoDecl _ p) = missingAna t p
anaTypeItem _ (SubtypeDefn t _ _ _ p) = missingAna t p
anaTypeItem _ (Datatype (DatatypeDecl t _ _ _ p)) = missingAna t p
anaTypeItem _ (AliasType t _ _ p) = missingAna t p

anaTypePattern :: Instance -> Kind -> TypePattern -> State Env ()
-- type args not yet considered for kind construction 
anaTypePattern _ kind t = 
    let Result ds mi = convertTypePattern t
    in if typePatternArgs t == 0 || 
       typePatternArgs t == kindArity kind then
       case mi of 
	       Just ti -> addTypeKind ti kind
	       Nothing -> appendDiags ds
       else appendDiags [Diag Error "non-matching kind arity"
					    $ posOfTypePattern t]

convertTypePattern, makeMixTypeId :: TypePattern -> Result Id
convertTypePattern (TypePattern t _ _) = return t
convertTypePattern(TypePatternToken t) = 
    if isPlace t then fatal_error ("illegal type '__'") (tokPos t)
       else return $ (simpleIdToId t)

convertTypePattern t =
    if hasPlaces t && hasTypeArgs t then
       fatal_error ( "illegal mix of '__' and '(...)'" ) 
                   (posOfTypePattern t)
    else makeMixTypeId t

typePatternToTokens :: TypePattern -> [Token]
typePatternToTokens (TypePattern ti _ _) = getTokenList True ti
typePatternToTokens (TypePatternToken t) = [t]
typePatternToTokens (MixfixTypePattern ts) = concatMap typePatternToTokens ts
typePatternToTokens (BracketTypePattern pk ts ps) =
    let tts = map typePatternToTokens ts 
	expand = expandPos (:[]) in
	case pk of 
		Parens -> if length tts == 1 && 
			  length (head tts) == 1 then head tts
			  else concat $ expand "(" ")" tts ps
		Squares -> concat $ expand "[" "]" tts ps 
		Braces ->  concat $ expand "{" "}" tts ps
typePatternToTokens (TypePatternArgs as) =
    map ( \ (TypeArg v _ _ _) -> Token "__" (tokPos v)) as

-- compound Ids not supported yet
getToken :: GenParser Token st Token
getToken = token tokStr (( \ (l, c) -> newPos "" l c) . tokPos) Just
parseTypePatternId :: GenParser Token st Id
parseTypePatternId =
    do ts <- many1 getToken 
       return $ Id ts [] []

makeMixTypeId t = 
    case parse parseTypePatternId "" (typePatternToTokens t) of
    Left err -> fatal_error (showErrorMessages "or" "unknown parse error" 
                             "expecting" "unexpected" "end of input"
			     (errorMessages err)) 
		(let p = errorPos err in (sourceLine p, sourceColumn p))
    Right x -> return x

typePatternArgs :: TypePattern -> Int
typePatternArgs (TypePattern _ as _) = length as
typePatternArgs (TypePatternToken t) = if isPlace t then 1 else 0
typePatternArgs (MixfixTypePattern ts) = sum (map typePatternArgs ts)
typePatternArgs (BracketTypePattern _ ts _) = sum (map typePatternArgs ts)
typePatternArgs (TypePatternArgs as) = length as

hasPlaces, hasTypeArgs :: TypePattern -> Bool
hasPlaces (TypePattern _ _ _) = False
hasPlaces (TypePatternToken t) = isPlace t
hasPlaces (MixfixTypePattern ts) = any hasPlaces ts
hasPlaces (BracketTypePattern Parens _ _) = False
hasPlaces (BracketTypePattern _ ts _) = any hasPlaces ts
hasPlaces (TypePatternArgs _) = False

hasTypeArgs (TypePattern _ _ _) = True
hasTypeArgs (TypePatternToken _) = False
hasTypeArgs (MixfixTypePattern ts) = any hasTypeArgs ts
hasTypeArgs (BracketTypePattern Parens _ _) = True
hasTypeArgs (BracketTypePattern _ ts _) = any hasTypeArgs ts
hasTypeArgs (TypePatternArgs _) = True
