
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
-- class instances
-----------------------------------------------------------------------------

type ClassInst    = ([Id], [Inst]) -- super classes and instances
type Inst     = Qual Pred

showInst :: Inst -> ShowS
showInst = showQual showPred

showClassInst :: ClassInst -> ShowS
showClassInst (sups, insts) =
    noShow (null sups) (showString "super classes: " . 
			showSepList (showString ",") showId sups)
    . noShow (null insts) (showString "\ninstances: " .
			showSepList (showString ",") showInst insts)

-----------------------------------------------------------------------------

type ClassEnv = FiniteMap Id ClassInst

super     :: ClassEnv -> Id -> [Id]
super ce i = case lookupFM ce i of Just (is, _) -> is
				   Nothing -> []

insts     :: ClassEnv -> Id -> [Inst]
insts ce i = case lookupFM ce i of Just (_, its) -> its
				   Nothing -> []


-----------------------------------------------------------------------------
-- assumptions
-----------------------------------------------------------------------------

type Assumps = FiniteMap Id [Scheme]


-----------------------------------------------------------------------------
-- local env
-----------------------------------------------------------------------------

data Env = Env { classenv :: ClassEnv
	       , assumps :: Assumps
	       , diags :: [Diagnosis]
	       } deriving Show

showEnv e = showMap showId showClassInst (classenv e) .
	    showString "\nAssumptions\n" .
	    showMap showId (showSepList (showString ", ") showScheme) 
		    (assumps e) .
	    showChar '\n' .
	    showList (reverse $ diags e)


----------------------------------------------------------------------------
-- analysis
-----------------------------------------------------------------------------

writeMsg e s = put (e {diags = s : diags e})

anaBasicSpec (BasicSpec l) = mapM_ anaAnnotedBasicItem l

anaAnnotedBasicItem i = anaBasicItem $ item i 

anaBasicItem (SigItems i) = anaSigItems i
anaBasicItem (ClassItems inst l _) = mapM_ (anaAnnotedClassItem inst) l
anaBasicItem (GenVarItems l _) = mapM_ anaGenVarDecl l

anaSigItems(TypeItems inst l _) = mapM_ (anaAnnotedTypeItem inst) l

anaGenVarDecl(GenVarDecl v) = optAnaVarDecl v
anaGenVarDecl(GenTypeVarDecl t) = anaTypeDecl t

optAnaVarDecl = error "nyi"
anaTypeDecl = error "nyi"

anaAnnotedClassItem inst aci = 
    let As.ClassItem d l _ = item aci in
    do anaClassDecls d 
       mapM_ anaAnnotedBasicItem l

anaClassDecls (ClassDecl cls _) = mapM_ (anaClassDecl []) cls
anaClassDecls (SubclassDecl cls supcl _) =
    do scls <- anaSupClass supcl
       mapM_ (anaClassDecl scls) cls
	       
anaSupClass (As.ClassName c) = 
    do anaClassDecl [] c
       return [simpleIdToId c]

anaSupClass (As.Intersection cs _) = 
    do cs <- mapM anaSupClass cs
       return $ nub $ concat cs

anaSupClass (As.Universe p) =
    do e <- get
       writeMsg e (Warning "redundant universe class" p)
       return []

anaClassDecl l t = 
    let i = simpleIdToId t
    in do e <- get
	  let cs = classenv e 
	      m = lookupFM cs i 
	    in case m of 
	    Nothing -> put (e {classenv = addToFM cs i (l, [])})
	    Just (sups, insts) -> 
		do writeMsg e (Warning ("redeclared class '"
					++ showId i "'") 
			      $ posOfId i)
		   if null l then return ()
		      else 
		      do e1 <- get
			 put (e1 {classenv = addToFM cs i 
				  (nub (l ++ sups), insts)})
			 let ds = filter (`elem` sups) l in
			     if null $ ds then return ()
				else 
				do e2 <- get
				   writeMsg e2 (Warning 
						("repeated superclass(es) '"
						 ++ showSepList (showString ",")
						 showId ds "'") 
					       $ posOfId (head ds))

anaAnnotedTypeItem inst i = anaTypeItem inst $ item i

anaTypeItem inst (TypeDecl pats kind _) = 
    mapM_ (anaTypePattern inst kind) pats 

anaTypePattern inst kind (TypePatternToken t) = 
    let i = simpleIdToId t
    in 
    do k <- anaPlainKind kind
       let ty = [] :=> TCon (Tycon i k)
	 in do addTypeScheme i (Scheme [] ty)
	       anaKind kind ty
       

anaPlainKind (Kind [] _  _) = return star 
anaKind (Kind [] (As.Universe _) _) _ = return ()
anaKind (Kind [] (As.ClassName ci) _) (qs :=> t) = 
    let i = simpleIdToId ci in
    do e <- get
       let cs = classenv e 
           m = lookupFM cs i 
	 in case m of 
	    Nothing -> writeMsg e (Error ("undeclared class '"
					  ++ showId i "'")
				   $ posOfId i)
	    Just (sc, is) -> put (e {classenv =
				     addToFM cs i (sc, 
						   (qs :=> 
						    (i `IsIn` t))
						   : is)})


-- addTypeScheme :: Id -> Scheme -> State Env ()
addTypeScheme i sc = do 
		     e <- get 
		     let as = assumps e 
                         l = lookUp as i in
                       if sc `elem` l then
			  writeMsg e (Warning ("repeated declaration for '" 
					       ++ showId i "'")
				     $ posOfId i)
		       else put (e {assumps = addToFM as i (sc:l)})
