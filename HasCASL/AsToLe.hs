
{- HetCATS/HasCASL/AsToLe.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   conversion of As.hs to Le.hs
-}

module AsToLe where

import AS_Annotation
import As
import AsUtils
import ClassDecl
import Le
import Id
import Monad
import MonadState
import FiniteMap
import Result
import Maybe
import ParseTerm(isSimpleId)
import MixfixParser(getTokenList, expandPos)
import Parsec
import ParsecPos
import ParsecError
import TypeAna

----------------------------------------------------------------------------
-- analysis
-----------------------------------------------------------------------------

anaBasicSpec :: BasicSpec -> State Env ()
anaBasicSpec (BasicSpec l) = mapM_ anaAnnotedBasicItem l

anaAnnotedBasicItem :: Annoted BasicItem -> State Env ()
anaAnnotedBasicItem i = anaBasicItem $ item i 

anaBasicItem :: BasicItem -> State Env ()
anaBasicItem (SigItems i) = anaSigItems i
anaBasicItem (ClassItems inst l _) = mapM_ (anaAnnotedClassItem inst) l
anaBasicItem (GenVarItems l _) = mapM_ anaGenVarDecl l

anaSigItems :: SigItems -> State Env ()
anaSigItems(TypeItems inst l _) = mapM_ (anaAnnotedTypeItem inst) l

----------------------------------------------------------------------------
-- GenVarDecl
-----------------------------------------------------------------------------

anaGenVarDecl :: GenVarDecl -> State Env ()
anaGenVarDecl(GenVarDecl v) = optAnaVarDecl v
anaGenVarDecl(GenTypeVarDecl t) = anaTypeVarDecl t

convertTypeToClass :: ClassMap -> Type -> Result Class
convertTypeToClass cMap (TypeToken t) = 
       if tokStr t == "Type" then Result [] (Just $ universe) else 
	  let ci = simpleIdToId t
	      ds = anaClassId cMap ci
	      in if null ds then 
		 Result [] (Just $ Intersection [ci] [])
		 else Result ds Nothing

convertTypeToClass cMap (BracketType Parens ts ps) = 
       let is = map (convertTypeToClass cMap) ts
	   mis = map maybeResult is
	   ds = concatMap diags is
	   in if all isJust mis then Result ds 
	      (Just $ Intersection (concatMap (iclass . fromJust) mis) ps)
	      else Result ds Nothing

convertTypeToClass _ _ = Result [] Nothing

optAnaVarDecl, anaVarDecl :: VarDecl -> State Env ()
optAnaVarDecl vd@(VarDecl v t _ _) = 
    if isSimpleId v then
       do cMap <- getClassMap 
	  let Result _ mc = convertTypeToClass cMap t 
	      in case mc of
	       Just c -> addTypeKind v (Kind [] c [])
	       Nothing -> anaVarDecl vd
    else anaVarDecl vd

anaVarDecl(VarDecl v oldT _ p) = 
		   do t <- anaType oldT
		      as <- getAssumps
		      let l = lookupWithDefaultFM as [] v 
			  ts = SimpleTypeScheme t in 
			  if ts `elem` l then 
			     appendDiags 
				     [Diag Warning 
				      ("repeated variable '" 
				       ++ showId v "'") p ]
			     else  putAssumps $ addToFM as v (ts:l)

anaTypeVarDecl :: TypeVarDecl -> State Env ()
anaTypeVarDecl(TypeVarDecl t k _ _) = 
    do nk <- anaKind k
       addTypeKind t k
       addTypeVar t
-- ------------------------------------------------------------------------------ ClassItem
-- ----------------------------------------------------------------------------

anaAnnotedClassItem :: Instance -> Annoted ClassItem -> State Env ()
anaAnnotedClassItem _ aci = 
    let ClassItem d l _ = item aci in
    do anaClassDecls d 
       mapM_ anaAnnotedBasicItem l

-- ----------------------------------------------------------------------------
-- TypeItem
-- ----------------------------------------------------------------------------

anaAnnotedTypeItem :: Instance -> Annoted TypeItem -> State Env ()
anaAnnotedTypeItem inst i = anaTypeItem inst $ item i

anaTypeItem :: Instance -> TypeItem -> State Env ()
anaTypeItem inst (TypeDecl pats kind _) = 
    do k <- anaKind kind
       mapM_ (anaTypePattern inst k) pats 

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

-- ----------------------------------------------------------------------------
-- addTypeKind
-- ----------------------------------------------------------------------------

addTypeKind :: Id -> Kind -> State Env ()
addTypeKind t k = 
    do tk <- getTypeKinds
       case lookupFM tk t of
            Just ks -> do appendDiags [Diag Warning 
				       ("shadowing type '" 
					++ showId t "'") 
				      $ posOfId t]
			  putTypeKinds $ addToFM tk t (k:ks)
	    _ -> putTypeKinds $ addToFM tk t [k]

{- 
-- add instances later on
	  let ce = classEnv e 
	      mc = lookupFM ce ci 
	    in case mc of 
	       Nothing -> do appendDiags [Error ("undeclared class '"
					     ++ tokStr c ++ "'")
				     $ tokPos c]
			     return star
	       Just info -> do put $ e { classEnv =
				      addToFM ce ci info 
				      { instances = 
					[] :=> (ci `IsIn` TCon (Tycon t k))
					: instances info } }
			       return k
-}

