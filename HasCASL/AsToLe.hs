
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
import Le
import Id
import Monad
import MonadState
import FiniteMap
import Result
import List(nub, partition)
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

convertTypeToClass :: Type -> State Env (Result Class)
convertTypeToClass (TypeToken t) = 
    do if tokStr t == "Type" then return $ Result [] (Just $ universe) else 
	  do Result ds (Just cs) <- anaClassName False t 
	     if null cs then return $ Result ds Nothing
		else return $ Result ds (Just $ Intersection cs [])  

convertTypeToClass (BracketType Parens ts ps) = 
    do is <- mapM convertTypeToClass ts
       let mis = map maybeResult is
	   ds = concatMap diags is
	   in if all isJust mis then return $ Result ds 
	      (Just $ Intersection (concatMap (iclass . fromJust) mis) ps)
	      else return $ Result ds Nothing

convertTypeToClass _ = return $ Result [] Nothing

optAnaVarDecl, anaVarDecl :: VarDecl -> State Env ()
optAnaVarDecl vd@(VarDecl v t _ _) = 
    if isSimpleId v then
       do Result ds mc <- convertTypeToClass t
	  case mc of
	       Just c -> addTypeKind v (Kind [] c [])
	       Nothing -> anaVarDecl vd
    else anaVarDecl vd

anaVarDecl(VarDecl v oldT _ p) = 
		   do t <- anaType oldT
		      as <- getAssumps
		      let l = lookUp as v 
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
-- ------------------------------------------------------------------------------ As.ClassItem
-- ----------------------------------------------------------------------------

anaAnnotedClassItem :: Instance -> Annoted As.ClassItem -> State Env ()
anaAnnotedClassItem _ aci = 
    let As.ClassItem d l _ = item aci in
    do anaClassDecls d 
       mapM_ anaAnnotedBasicItem l

anaClassDecls :: ClassDecl -> State Env ()
anaClassDecls (ClassDecl cls _) = 
    mapM_ (anaClassDecl [] universe) cls

anaClassDecls (SubclassDecl cls supcl _) =
    do Intersection scls _ <- anaSuperClass supcl
       mapM_ (anaClassDecl scls universe) cls

anaClassDecls (ClassDefn ci syncl _) =
    do scls@(Intersection icls _) <- anaClassAppl syncl
       anaClassDecl [] scls ci

anaClassDecls (DownsetDefn ci _ t _) = 
    do newT <- anaType t 
       anaClassDecl [] (Downset newT) ci

anaSuperClass :: Class -> State Env Class
anaSuperClass c =
    anaClass True c 

anaClassDecl :: [ClassName] -> Class -> ClassName -> State Env ()
anaClassDecl cs cdef ci = 
    if tokStr ci == "Type" then 
       appendDiags [Diag Error 
		    "illegal universe class declaration" (tokPos ci)]
    else 
    do ce <- getClassEnv
       case lookupFM ce ci of 
	    Nothing -> putClassEnv $ defCEntry ce ci 
				 cs cdef
	    Just info -> do 
	      appendDiags [Diag Warning ("redeclared class '"
					 ++ tokStr ci ++ "'") 
			  $ tokPos ci]
	      let oldCs = superClasses info
		  oldDefn = classDefn info in
		if null cs then 
		   do newDefn <- mergeDefn ce ci oldDefn cdef
		      putClassEnv $ addToFM ce ci 
				  info { classDefn = newDefn }
		else 
		   do newCs <- getLegalSuperClasses ce ci oldCs cs
		      putClassEnv $ addToFM ce ci 
				  info { superClasses = newCs }
 
getLegalSuperClasses ce ci oldCs cs =
    let scs = zip (map (allSuperClasses ce) cs) cs
	(scycs, sOk) = partition ((ci `elem`) . fst) scs
	defCs = map snd sOk
	newCs = nub $ defCs ++ oldCs
	cycles = map snd scycs
        dubs = filter (`elem` oldCs) defCs
    in do if null cycles then return ()
	     else appendDiags 
		      [Diag Error 
		       ("cyclic class relation via '"
			++ showClassList cycles "'")
		      $ tokPos (head cycles)]
	  if null dubs then return ()
	     else appendDiags 
		      [Diag Warning 
		       ("repeated class '"
			++ showClassList dubs "'")
		      $ tokPos (head dubs)]
	  return newCs

mergeDefn _ ci (Downset oldT) c@(Downset t) =
    do if eqType oldT t then return () 
	  else incompatibleClassRedeclaration ci
       return c

mergeDefn ce ci (Intersection oldIs qs) (Intersection is ps) =
    do iss <- getLegalSuperClasses ce ci oldIs is
       return $ Intersection iss $ ps ++ qs

mergeDefn _ ci _ c =
    do incompatibleClassRedeclaration ci
       return c

incompatibleClassRedeclaration ci =
    appendDiags [Diag Warning 
		 ("incompatible redeclaration of '" ++ tokStr ci ++ "'")
		 $ tokPos ci]

-- ----------------------------------------------------------------------------
-- TypeItem
-- ----------------------------------------------------------------------------

anaAnnotedTypeItem :: Instance -> Annoted As.TypeItem -> State Env ()
anaAnnotedTypeItem inst i = anaTypeItem inst $ item i

anaTypeItem :: Instance -> As.TypeItem -> State Env ()
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
            Just _ -> appendDiags [Diag Warning 
				   ("shadowing type '" 
				    ++ showId t "'") 
				  $ posOfId t]
	    _ -> return ()
       putTypeKinds $ addToFM tk t k

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

