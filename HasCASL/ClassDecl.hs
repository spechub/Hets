{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 

   analyse class decls
-}

module HasCASL.ClassDecl where

import HasCASL.As
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.Id
import HasCASL.Le
import Data.List
import Data.Maybe
import Common.Lib.State
import Common.Result
import HasCASL.ClassAna


-- ---------------------------------------------------------------------------
-- analyse class decls
-- ---------------------------------------------------------------------------

anaClassDecls :: ClassDecl -> State Env ()
anaClassDecls (ClassDecl cls k _) = 
    do ak <- anaKind k
       mapM_ (addClassDecl ak Set.empty Nothing) cls

anaClassDecls (SubclassDecl _ _ (Downset _) _) = error "anaClassDecl"
anaClassDecls (SubclassDecl cls k sc@(Intersection supcls ps) qs) =
    do ak <- anaKind k
       if Set.isEmpty supcls then 
	  do addDiags [Diag Warning
			  "redundant universe class" 
			 $ headPos (ps ++ qs)]
	     mapM_ (addClassDecl ak supcls Nothing) cls
          else let (hd, tl) = Set.deleteFindMin supcls in 
	      if Set.isEmpty tl then
		 do b <- isClassId hd
		    if b then
		       return () else do  
			  addClassDecl ak tl Nothing hd
			  addDiags [mkDiag Warning 
				      "implicit declaration of superclass" hd]
		    mapM_ (addClassDecl ak (Set.single hd) Nothing) cls
		  else do (sk, Intersection newSups _) <- anaClass sc
			  checkKinds hd sk ak
			  mapM_ (addClassDecl ak newSups Nothing) cls

anaClassDecls (ClassDefn ci k ic _) =
    do ak <- anaKind k
       (dk, newIc) <- anaClass ic
       checkKinds ci dk ak
       addClassDecl ak Set.empty (Just newIc) ci 

anaClassDecls (DownsetDefn ci _ t _) = 
    do addDiags [downsetWarning t]
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
       addDiags [mkDiag Error 
		    "illegal universe class declaration" ci]
    else do
       cMap <- gets classMap
       case Map.lookup ci cMap of
            Nothing -> putClassMap $ Map.insert ci  
		       newClassInfo { superClasses = sups,
				      classKind = kind,
					   classDefn = defn } cMap
	    Just info -> do 
	        addDiags [mkDiag Warning "redeclared class" ci]
		let oldDefn = classDefn info
		    oldSups = superClasses info
		    oldKind = classKind info
		checkKinds ci kind oldKind
		if isJust defn then
		   if isJust oldDefn then
		      addDiags $ mergeDefns ci 
				      (fromJust oldDefn) (fromJust defn)
		      else addDiags [mkDiag Error
			     "class cannot become an alias class" ci]
		      else if isJust oldDefn then
			   addDiags [mkDiag Error 
			     "alias class cannot become a real class" ci]
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
		    else addDiags [myDiag Error 
			      "cyclic class relation via" cycles]
		 if null dubs then return ()
		    else addDiags [myDiag Warning 
			      "already known as super class" dubs]
		 return newCs

showClassList :: [ClassId] -> ShowS
showClassList is = showParen (not $ isSingle is)
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
