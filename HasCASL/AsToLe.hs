
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

type TypeKinds = FiniteMap TypeName [Kind]

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

getTypeKinds :: State Env TypeKinds
getTypeKinds = gets typeKinds

putTypeKinds :: TypeKinds -> State Env ()
putTypeKinds tk =  do { e <- get; put e { typeKinds = tk } }

putClassEnv :: ClassEnv -> State Env ()
putClassEnv ce = do { e <- get; put e { classEnv = ce } }

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

anaGenVarDecl :: GenVarDecl -> State Env ()
anaGenVarDecl(GenVarDecl v) = optAnaVarDecl v
anaGenVarDecl(GenTypeVarDecl t) = anaTypeVarDecl t

optAnaVarDecl :: VarDecl -> State Env ()
optAnaVarDecl =		 error "nyi"

{-
optAnaVarDecl(VarDecl v t _ _) = 
    let mc = TypeToClass t in 
	     if isSimpleId v && isJust mc then
		ana

-}

anaTypeVarDecl :: TypeVarDecl -> State Env ()
anaTypeVarDecl = error "nyi"

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

anaClass _ (Downset _) = error "must not happen"

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
		in do appendDiags [Warning ("redeclared class '"
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
					 ("repeated superclass declaration '"
					  ++ showClassList ds "'")
					$ tokPos (head ds)]
		      if null oldIs then return ()
			     else appendDiags
					[Warning 
					 ("merged definition '"
					  ++ showClassList defIs "'")
					$ tokPos (head defIs)]

-- ----------------------------------------------------------------------------
-- TypeItem
-- ----------------------------------------------------------------------------

anaAnnotedTypeItem :: Instance -> Annoted As.TypeItem -> State Env ()
anaAnnotedTypeItem inst i = anaTypeItem inst $ item i

anaTypeItem :: Instance -> As.TypeItem -> State Env ()
anaTypeItem inst (TypeDecl pats kind _) = 
    mapM_ (anaTypePattern inst kind) pats 

anaTypePattern :: Instance -> Kind -> TypePattern -> State Env ()
anaTypePattern _ kind (TypePatternToken t) = 
    do k <- anaKind kind
       addTypeKind (simpleIdToId t) k

addTypeKind :: Id -> Kind -> State Env ()
addTypeKind t k = 
    do tk <- getTypeKinds
       let l = lookUp tk t in
	 if k `elem` l then
	    appendDiags [Warning ("redeclared type '" 
					       ++ showId t "'")
				     $ posOfId t]
		       else putTypeKinds $ addToFM tk t (k:l)

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


