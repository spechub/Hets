
{- HetCATS/HasCASL/AsToLe.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   conversion of As.hs to Le.hs
-}

module AsToLe where

import AS_Annotation
import As
import Le
import Id
import Monad
import MonadState
import FiniteMap
import Result
import List
import Maybe
import ParseTerm(isSimpleId)

----------------------------------------------------------------------------
-- FiniteMap stuff
-----------------------------------------------------------------------------

lookUp :: (Ord a, MonadPlus m) => FiniteMap a (m b) -> a -> (m b)
lookUp ce = lookupWithDefaultFM ce mzero

showMap :: Ord a => (a -> ShowS) -> (b -> ShowS) -> FiniteMap a b -> ShowS
showMap showA showB m =
    showSepList (showChar '\n') (\ (a, b) -> showA a . showString " -> " .
				 indent 2 (showB b))
				 (fmToList m) 

-----------------------------------------------------------------------------

indent :: Int -> ShowS -> ShowS
indent i s = showString $ concat $ 
	     intersperse ('\n' : replicate i ' ') (lines $ s "")

-----------------------------------------------------------------------------

type ClassEnv = FiniteMap ClassName Le.ClassItem

-- transitiv super classes 
-- PRE: all superclasses and defns must be defined in ClassEnv
-- and there must be no cycle!
allSuperClasses :: ClassEnv -> ClassName -> [ClassName]
allSuperClasses ce ci = 
    case lookupFM ce ci of 
    Just info -> nub $
		      ci: concatMap (allSuperClasses ce) (iclass $ 
							  classDefn info) 
		      ++  concatMap (allSuperClasses ce) (superClasses info)
    Nothing -> error "allSuperClasses"

defCEntry :: ClassEnv -> ClassName  -> [ClassName] -> Class -> ClassEnv
defCEntry ce cid sups defn = addToFM ce cid 
			   (newClassItem cid) { superClasses = sups
					      , classDefn = defn } 

-----------------------------------------------------------------------------
-- assumptions
-----------------------------------------------------------------------------

type Assumps = FiniteMap Id [TypeScheme]

type TypeKinds = FiniteMap TypeName Kind

-----------------------------------------------------------------------------
-- local env
-----------------------------------------------------------------------------

data Env = Env { classEnv :: ClassEnv
               , typeKinds :: TypeKinds
	       , assumps :: Assumps
	       , envDiags :: [Diagnosis]
	       } deriving Show

initialEnv :: Env
initialEnv = Env emptyFM emptyFM emptyFM []

appendDiags :: [Diagnosis] -> State Env ()
appendDiags ds =
    if null ds then return () else
    do e <- get
       put $ e {envDiags = ds ++ envDiags e}


getClassEnv :: State Env ClassEnv
getClassEnv = gets classEnv

putClassEnv :: ClassEnv -> State Env ()
putClassEnv ce = do { e <- get; put e { classEnv = ce } }

getTypeKinds :: State Env TypeKinds
getTypeKinds = gets typeKinds

putTypeKinds :: TypeKinds -> State Env ()
putTypeKinds tk =  do { e <- get; put e { typeKinds = tk } }

getAssumps :: State Env Assumps
getAssumps = gets assumps

putAssumps :: Assumps -> State Env ()
putAssumps as =  do { e <- get; put e { assumps = as } }


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
    do Result ds (Just cs) <- anaClassName False t 
       if null cs then return $ Result ds Nothing
	  else return $ Result ds (Just $ Intersection cs [])  

convertTypeToClass (BracketType Parens ts ps) = 
    convertTypeListToClass ts ps

convertTypeToClass (TupleType ts ps) = convertTypeListToClass ts ps

convertTypeToClass _ = return $ Result [] Nothing

convertTypeListToClass :: [Type] -> [Pos] -> State Env (Result Class)
convertTypeListToClass ts ps =
    do is <- mapM convertTypeToClass ts
       let mis = map maybeResult is
	   ds = concatMap diags is
	   in if all isJust mis then return $ Result ds 
	      (Just $ Intersection (concatMap (iclass . fromJust) mis) ps)
	      else return $ Result ds Nothing

optAnaVarDecl, anaVarDecl :: VarDecl -> State Env ()
optAnaVarDecl vd@(VarDecl v t _ _) = 
    if isSimpleId v then
       do Result ds mc <- convertTypeToClass t
	  case mc of
	       Just c -> addTypeKind v (Kind [] c [])
	       Nothing -> anaVarDecl vd
    else anaVarDecl vd

anaVarDecl(VarDecl v t _ p) = 
		   do as <- getAssumps
		      let l = lookUp as v 
			  ts = SimpleTypeScheme t in 
			  if ts `elem` l then 
			     appendDiags 
				     [Warning 
				      ("repeated variable '" 
				       ++ showId v "'") p ]
			     else  putAssumps $ addToFM as v (ts:l)

anaTypeVarDecl :: TypeVarDecl -> State Env ()
anaTypeVarDecl(TypeVarDecl t k _ _) = 
    do nk <- anaKind k
       addTypeKind t k

-- ----------------------------------------------------------------------------
-- As.ClassItem
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

anaClassDecls (DownsetDefn ci tv _ _) = 
    do anaClassDecl [] universe ci
       appendDiags [Warning "definition currently ignored" (tokPos tv)]
	       
anaClassName :: Bool -> ClassName -> State Env (Result [ClassName])
-- True: declare the class
anaClassName b ci = 
    do ce <- getClassEnv
       if isJust $ lookupFM ce ci then return $ return [ci]
	 else if b then 
		do putClassEnv $ defCEntry ce ci [] universe
                   return $ return [ci]
	      else 	  
		return $ non_fatal_error [] 
		    ("undeclared class '" ++ tokStr ci ++  "'")
		    (tokPos ci)

anaClass :: Bool -> Class -> State Env (Result Class)
anaClass b c@(As.Intersection cs ps) = 
    if null cs
       then if null ps then return $ return c  -- no warning 
	    else return $ warning c "redundant universe class" (head ps)
       else
    do newCs <- mapM (anaClassName (b && null (tail cs))) cs
       return $ Result (concatMap diags newCs) 
		  (Just $ Intersection 
		   (nub $ concatMap (fromJust . maybeResult) newCs) ps)

anaClass _ (Downset _) = error "anaClass for Downset"

anaSuperClass :: Class -> State Env Class
anaSuperClass c =
    do Result ds (Just ca) <- anaClass True c 
       appendDiags ds
       return ca

anaClassAppl :: Class -> State Env Class
anaClassAppl c =
    do Result ds (Just ca) <- anaClass False c
       appendDiags ds
       return ca

anaClassDecl :: [ClassName] -> Class -> ClassName -> State Env ()
anaClassDecl cs cdef@(Intersection is ps) ci = 
    if tokStr ci == "Type" then 
       appendDiags [Error "illegal universe class declaration" (tokPos ci)]
    else 
    do ce <- getClassEnv
       case lookupFM ce ci of 
	    Nothing -> putClassEnv $ defCEntry ce ci 
				 cs cdef
	    Just info -> 
		let getSups = allSuperClasses ce
		    checkCycle = (ci `elem`) . fst
		    scs = zip (map getSups cs) cs
		    (scycs, sOk) = partition checkCycle scs
		    oldCs = superClasses info
		    iss = zip (map getSups is) is
		    (icycs, iOk) = partition checkCycle iss
		    Intersection oldIs qs = classDefn info
		    defCs = map snd sOk
		    newCs = nub $ defCs ++ oldCs
		    defIs = map snd iOk
		    newIs = Intersection (nub $ defIs ++ oldIs) 
			       (ps ++ qs)
		    cycles = map snd $ scycs ++ icycs
		in do appendDiags [Warning ("repeated class '"
					++ tokStr ci ++ "'") 
			      $ tokPos ci]
		      if not $ null cycles then
			      appendDiags 
			      [Error 
			       ("cyclic class relation via '"
				      ++ showClassList cycles "'")
			      $ tokPos (head cycles)]
			   else return ()  
		      putClassEnv $ addToFM ce ci 
				  (info { superClasses = newCs, 
					  classDefn = newIs })
		      let ds = filter (`elem` oldCs) defCs in
			    if null ds then return ()
			       else appendDiags 
					[Warning 
					 ("repeated superclass '"
					  ++ showClassList ds "'")
					$ tokPos (head ds)]
		      if null oldIs then return ()
			     else appendDiags
					[Warning 
					 ("merged definition '"
					  ++ showClassList defIs "'")
					$ tokPos (head defIs)]

anaClassDecl _ (Downset _) _ = error "anaClassDecl for Downset"

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
anaTypePattern _ kind (TypePatternToken t) = 
       addTypeKind (simpleIdToId t) kind

convertTypePattern :: TypePattern -> Result TypePattern
convertTypePattern t@(TypePattern _ _ _) = return t
convertTypePattern(TypePatternToken t) = 
    if isPlace t then fatal_error ("illegal type '__'") (tokPos t)
       else return $ TypePattern (simpleIdToId t) [] []

convertTypePattern t =
    if hasPlaces t && hasTypeArgs t then
       fatal_error ( "illegal mix of '__' and '(...)'" ) 
                   (posOfTypePattern t)
    else error "nyi" -- makeMixTypeId t

posOfTypePattern :: TypePattern -> Pos
posOfTypePattern (TypePattern t _ _) = posOfId t
posOfTypePattern (TypePatternToken t) = tokPos t
posOfTypePattern (MixfixTypePattern ts) = 
    if null ts then nullPos else posOfTypePattern $ head ts
posOfTypePattern (BracketTypePattern _ ts ps) = 
    if null ps then 
       if null ts then nullPos
       else posOfTypePattern $ head ts
    else head ps
posOfTypePattern (TypePatternArgs as) = 
    if null as then nullPos else 
       let TypeArg t _ _ _ = head as in tokPos t
		    
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
            Just _ -> appendDiags [Warning 
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

-- ----------------------------------------------------------------------------
-- Kind
-- ----------------------------------------------------------------------------

anaKind :: Kind -> State Env Kind
anaKind (KindAppl k1 k2) =
    do n1 <- anaKind k1
       n2 <- anaKind k2
       return $ KindAppl n1 n2
anaKind (Kind args c p) = 
    do ca <- anaClassAppl c
       newArgs <- mapM anaProdClass args
       return $ Kind newArgs ca p

anaExtClass :: ExtClass -> State Env ExtClass
anaExtClass (ExtClass c v p) = 
    do ca <- anaClassAppl c
       return $ ExtClass ca v p

anaProdClass :: ProdClass -> State Env ProdClass
anaProdClass (ProdClass l p) =
    do cs <- mapM anaExtClass l
       return $ ProdClass cs p


