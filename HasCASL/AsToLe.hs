
{- HetCATS/HasCASL/AsToLe.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   conversion of As.hs to Le.hs
-}

module AsToLe where

import AS_Annotation
import As
import Id
import Le
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

type ClassEnv = FiniteMap ClassId Le.ClassItem

-- transitiv super classes 
-- PRE: all superclasses and defns must be defined in ClassEnv
-- and there must be no cycle!
allSuperClasses :: ClassEnv -> ClassId -> [ClassId]
allSuperClasses ce ci = 
    case lookupFM ce ci of 
    Just info -> nub $
		      ci: concatMap (allSuperClasses ce) (classDefn info) 
		      ++  concatMap (allSuperClasses ce) (superClasses info)
    Nothing -> error "allSuperClasses"

addToCE ce cid sups defn = addToFM ce cid 
			   (newClassItem cid) { superClasses = sups
					      , classDefn = defn } 

-----------------------------------------------------------------------------
-- assumptions
-----------------------------------------------------------------------------

type Assumps = FiniteMap Id [Scheme]

type TypeKinds = FiniteMap TypeId [Le.Kind]


-----------------------------------------------------------------------------
-- local env
-----------------------------------------------------------------------------

data Env = Env { classEnv :: ClassEnv
               , typeKinds :: TypeKinds
	       , assumps :: Assumps
	       , envDiags :: [Diagnosis]
	       } 

initialEnv = Env emptyFM emptyFM emptyFM []


showEnv e = showMap showId showClassItem (classEnv e) .
	    showString "\nType Constructors\n" .
	    showMap showId (showSepList (showString ", ") showKind)
		    (typeKinds e) .
	    showString "\nAssumptions\n" .
	    showMap showId (showSepList (showString ", ") showScheme) 
		    (assumps e) .
	    showChar '\n' .
	    showList (reverse $ envDiags e)

appendDiags ds =
    if null ds then return () else
    do e <- get
       put $ e {envDiags = ds ++ envDiags e}

----------------------------------------------------------------------------
-- analysis
-----------------------------------------------------------------------------

writeMsg e s = put $ e {envDiags = s : envDiags e}

anaBasicSpec (BasicSpec l) = mapM_ anaAnnotedBasicItem l

anaAnnotedBasicItem i = anaBasicItem $ item i 

anaBasicItem (SigItems i) = anaSigItems i
anaBasicItem (ClassItems inst l _) = mapM_ (anaAnnotedClassItem inst) l
anaBasicItem (GenVarItems l _) = mapM_ anaGenVarDecl l

anaSigItems(TypeItems inst l _) = mapM_ (anaAnnotedTypeItem inst) l

anaGenVarDecl(GenVarDecl v) = optAnaVarDecl v
anaGenVarDecl(GenTypeVarDecl t) = anaTypeDecl t

optAnaVarDecl =		 error "nyi"

{-
optAnaVarDecl(VarDecl v t _ _) = 
    let mc = TypeToClass t in 
	     if isSimpleId v && isJust mc then
		ana

-}

anaTypeDecl= error "nyi"


anaAnnotedClassItem inst aci = 
    let As.ClassItem d l _ = item aci in
    do anaClassDecls d 
       mapM_ anaAnnotedBasicItem l

anaClassDecls (ClassDecl cls _) = mapM_ (anaClassDecl []) cls
anaClassDecls (SubclassDecl cls supcl _) =
    do Result ds (Just scls) <- anaClass True supcl
       appendDiags ds
       mapM_ (anaClassDecl scls) cls


anaClassDecls (ClassDefn c syncl _) =
    do Result ds (Just scls) <- anaClass False syncl
       appendDiags ds
       e <- get
       let ci = simpleIdToId c
           ce = classEnv e
           mc = lookupFM ce ci in 
	 case mc of 
	   Nothing -> put $ e { classEnv = addToCE ce ci [] scls }
	   Just info -> 
	     do writeMsg e (Warning ("redeclared class '"
				    ++ showId ci "'") 
			  $ posOfId ci)
	        let supers = zip (map (allSuperClasses ce) scls) scls 
		    (cycles, nocycles) = partition ((ci `elem`) . fst) supers in 
		  do if not $ null cycles then
		       appendDiags [Error 
				    ("cyclic class definition via '"
				     ++ showClassList (map snd cycles) "'")
				   $ posOfId (snd $ head cycles)]
		       else return ()  
		     e1 <- get
		     put $ e1 { classEnv = addToFM ce ci 
				info { classDefn = nub $ map snd nocycles 
							 ++ classDefn info }
			      }
	       
anaClass b (As.ClassName c) = 
    do e <- get
       let ci = simpleIdToId c
           ce = classEnv e
           mc = lookupFM ce ci in 
	 if isJust mc then return $ return [ci]
	 else if b then 
		do put $ e { classEnv = addToCE ce ci [] [] }
                   return $ return [ci]
	      else 	  
		return $ non_fatal_error [] 
		    ("undeclared class '" ++ tokStr c ++  "'")
		    (tokPos c)

anaClass b (As.Intersection cs _) = 
    do cs <- mapM (anaClass False) cs
       return $ Result (concatMap diags cs) 
		  (Just $ nub $ concatMap (fromJust . maybeResult) cs)

anaClass _ (As.Universe p) =
    return $ warning [] "redundant universe class" p

anaClassDecl scls c = 
    do e <- get
       let ci = simpleIdToId c
           ce = classEnv e
           mc = lookupFM ce ci in 
	 case mc of 
	    Nothing -> put $ e { classEnv = addToCE ce ci scls [] }
	    Just info -> 
		do writeMsg e (Warning ("redeclared class '"
					++ showId ci "'") 
			      $ posOfId ci)
		   if null scls then return ()
		      else let supers = zip (map (allSuperClasses ce) scls) scls 
			       (cycles, nocycles) = 
				   partition ((ci `elem`) . fst) supers
			       sups = superClasses info in
		      do if not $ null cycles then
			      appendDiags 
			      [Error 
			       ("cyclic class relation via '"
				      ++ showClassList (map snd cycles) "'")
			      $ posOfId (snd $ head cycles)]
			   else return ()  
			 e1 <- get
			 put $ e1 { classEnv = addToFM ce ci 
				  (info { superClasses = 
					 nub $ map snd nocycles ++ sups }) }
			 let ds = filter (`elem` sups) scls in
			     if null $ ds then return ()
				else appendDiags [Warning 
						  ("repeated superclass '"
						   ++ showClassList ds "'")
						 $ posOfId (head ds)]

anaAnnotedTypeItem inst i = anaTypeItem inst $ item i

anaTypeItem inst (TypeDecl pats kind _) = 
    mapM_ (anaTypePattern inst kind) pats 

anaTypePattern inst kind (TypePatternToken t) = 
    let ty = simpleIdToId t
    in do k <- anaKind kind ty 
	  addTypeKind ty k

anaKind (Kind [] (As.Universe _) _) _ = return star
anaKind (Kind [] (As.ClassName c) _) t = 
    let ci = simpleIdToId c 
	k = Star $ ExtClass (Le.ClassName ci) InVar
    in do e <- get
	  let ce = classEnv e 
	      mc = lookupFM ce ci 
	    in case mc of 
	       Nothing -> do writeMsg e (Error ("undeclared class '"
					     ++ tokStr c ++ "'")
				     $ tokPos c)
			     return star
	       Just info -> do put $ e { classEnv =
				      addToFM ce ci info 
				      { instances = 
					[] :=> (ci `IsIn` TCon (Tycon t k))
					: instances info } }
			       return k

addTypeKind t k = 
    do e <- get 
       let tk = typeKinds e 
           l = lookUp tk t in
	 if k `elem` l then
	    writeMsg e (Warning ("redeclared type '" 
					       ++ showId t "'")
				     $ posOfId t)
		       else put $ e { typeKinds = addToFM tk t (k:l) }
