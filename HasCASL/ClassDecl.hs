
{- HetCATS/HasCASL/ClassDecl.hs
   $Id$
   Authors: Christian Maeder
   Year:    2003
   
   analyse class decls
-}

module HasCASL.ClassDecl where

import HasCASL.As
import HasCASL.AsUtils
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.Id
import HasCASL.Le
import Data.List
import Data.Maybe
import Common.Lib.State
import Common.Result
import Common.PrettyPrint
import HasCASL.ClassAna
import HasCASL.Reader

-- ---------------------------------------------------------------------------
-- state helpers
-- ---------------------------------------------------------------------------

-- ---------------------------------------------------------------------

toResultState :: (s -> r) -> ReadR r a -> State s (Result a) 
toResultState f m = State $ \s -> (readR m $ f s, s)

toMaybeState :: (Env -> r) -> ReadR r a -> State Env (Maybe a) 
toMaybeState f r = do Result ds m <- toResultState f r 
		      appendDiags ds 
		      return m

toState :: a -> (Env -> r) -> ReadR r a -> State Env a
toState d f r = do m <- toMaybeState f r
		   return $ case m of Nothing -> d
				      Just a -> a

-- ---------------------------------------------------------------------
-- adding diagnostic messages
-- ---------------------------------------------------------------------

appendDiags :: [Diagnosis] -> State Env ()
appendDiags ds =
    if null ds then return () else
    do e <- get
       put $ e {envDiags = ds ++ envDiags e}

addDiag :: Diagnosis -> State Env ()
addDiag d = appendDiags [d]

-- ---------------------------------------------------------------------------
-- analyse classes as state
-- ---------------------------------------------------------------------------

anaKindS :: Kind -> State Env Kind
anaKindS k = toState k classMap $ anaKind k 

anaClassS :: (Kind, Class) -> State Env (Kind, Class)
anaClassS c = toState c classMap $ anaClass $ snd c

checkKindsS :: (PosItem a, PrettyPrint a) => 
	       a -> Kind -> Kind -> State Env ()
checkKindsS p k1 k2 = do toMaybeState classMap $ checkKinds  p k1 k2
			 return ()

-- ---------------------------------------------------------------------------
-- analyse class decls
-- ---------------------------------------------------------------------------

anaClassDecls :: ClassDecl -> State Env ()
anaClassDecls (ClassDecl cls k _) = 
    do ak <- anaKindS k
       mapM_ (addClassDecl ak Set.empty Nothing) cls

anaClassDecls (SubclassDecl _ _ (Downset _) _) = error "anaClassDecl"
anaClassDecls (SubclassDecl cls k sc@(Intersection supcls ps) qs) =
    do ak <- anaKindS k
       if Set.isEmpty supcls then 
	  do addDiag $ Diag Warning
			  "redundant universe class" 
			 $ headPos (ps ++ qs)
	     mapM_ (addClassDecl ak supcls Nothing) cls
          else let (hd, tl) = Set.deleteFindMin supcls in 
	      if Set.isEmpty tl then
		 do Result _ mr <- toResultState classMap $ anaClassId hd
		    if isJust mr then
		       return () else do  
			  addClassDecl ak tl Nothing hd
			  addDiag $ mkDiag Warning 
				      "implicit declaration of superclass" hd
		    mapM_ (addClassDecl ak (Set.single hd) Nothing) cls
		  else do (sk, Intersection newSups _) <- anaClassS (ak, sc)
			  checkKindsS hd sk ak
			  mapM_ (addClassDecl ak newSups Nothing) cls

anaClassDecls (ClassDefn ci k ic _) =
    do ak <- anaKindS k
       (dk, newIc) <- anaClassS (ak, ic)
       checkKindsS ci dk ak
       addClassDecl ak Set.empty (Just newIc) ci 

anaClassDecls (DownsetDefn ci _ t _) = 
    do addDiag $ downsetWarning t
       addClassDecl star Set.empty (Just $ Downset t) ci

-- ---------------------------------------------------------------------------
-- store class decls
-- ---------------------------------------------------------------------------

-- | store a class map
putClassMap :: ClassMap -> State Env ()
putClassMap ce = do { e <- get; put e { classMap = ce } }

-- | store a class 
addClassDecl :: Kind -> Set.Set ClassId -> Maybe Class 
	     -> ClassId -> State Env ()
-- check with merge
addClassDecl kind sups defn ci = 
    if showId ci "" == "Type" then 
       addDiag $ Diag Error 
		    "illegal universe class declaration" $ posOfId ci
    else do
       cMap <- gets classMap
       case Map.lookup ci cMap of
            Nothing -> putClassMap $ Map.insert ci  
		       newClassInfo { superClasses = sups,
				      classKind = kind,
					   classDefn = defn } cMap
	    Just info -> do 
	        addDiag $ mkDiag Warning "redeclared class" ci
		let oldDefn = classDefn info
		    oldSups = superClasses info
		    oldKind = classKind info
		checkKindsS ci kind oldKind
		if isJust defn then
		   if isJust oldDefn then
		      appendDiags $ mergeDefns ci 
				      (fromJust oldDefn) (fromJust defn)
		      else addDiag $ mkDiag Error
			     "class cannot become an alias class" ci
		      else if isJust oldDefn then
			   addDiag $ mkDiag Error 
			     "alias class cannot become a real class" ci
		      else do
		      newSups <- getLegalSuperClasses cMap ci oldSups sups
		      putClassMap $ Map.insert ci info 
				      { superClasses = newSups } cMap

getLegalSuperClasses :: ClassMap -> ClassId -> Set.Set ClassId
		     -> Set.Set ClassId -> State Env (Set.Set ClassId)
getLegalSuperClasses ce ci oldCs ses =
       let cs = Set.toList ses
	   scs = zip (map (allSuperClasses ce) cs) cs
	   (scycs, sOk) = partition ((ci `Set.member`) . fst) scs
	   defCs = map snd sOk
	   newCs = Set.fromList defCs `Set.union` oldCs
	   cycles = map snd scycs
	   dubs = filter (`Set.member` allSuperClasses ce ci) defCs
	   myDiag k s l = Diag k (s ++ " '" ++ showClassList l "'")
			  $ posOfId $ head l
	   in do if null cycles then return ()
		    else addDiag $ myDiag Error 
			      "cyclic class relation via" cycles
		 if null dubs then return ()
		    else addDiag $ myDiag Warning 
			      "already known as super class" dubs
		 return newCs

showClassList :: [ClassId] -> ShowS
showClassList is = showParen (length is > 1)
		   $ showSepList ("," ++) showId is

-- check with merge
mergeDefns :: ClassId -> Class -> Class -> [Diagnosis]

mergeDefns ci (Downset oldT) (Downset t) =
    if oldT == t then [] else wrongClassDecl ci

mergeDefns ci (Intersection oldIs _) (Intersection is _) =
       if oldIs == is then []
	  else wrongClassDecl ci

mergeDefns ci _ _ = wrongClassDecl ci

wrongClassDecl :: ClassId -> [Diagnosis]
wrongClassDecl ci =
    [Diag Error 
		 ("inconsistent redefinition of '" ++ showId ci "'")
		 $ posOfId ci]
