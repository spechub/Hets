{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

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
import HasCASL.TypeAna
import HasCASL.Merge

-- ---------------------------------------------------------------------------
-- analyse class decls
-- ---------------------------------------------------------------------------

anaClassDecls :: ClassDecl -> State Env ClassDecl
anaClassDecls (ClassDecl cls k ps) = 
    do ak <- anaKind k
       mapM_ (addClassDecl ak Set.empty Nothing) cls
       return $ ClassDecl cls ak ps

anaClassDecls (SubclassDecl _ _ (Downset _) _) = error "anaClassDecl"
anaClassDecls (SubclassDecl cls k sc@(Intersection supcls ps) qs) =
    do ak <- anaKind k
       if Set.isEmpty supcls then 
	  do addDiags [Diag Warning
			  "redundant universe class" 
			 $ headPos (ps ++ qs)]
	     mapM_ (addClassDecl ak supcls Nothing) cls
	     return $ SubclassDecl cls ak sc qs
          else let (hd, tl) = Set.deleteFindMin supcls in 
	      if Set.isEmpty tl then
		 do e <- get 
		    mk <- anaClassId hd
		    case mk of 
			Nothing -> do 
			  put e
			  addClassDecl ak tl Nothing hd
			  addDiags [mkDiag Warning 
				      "implicit declaration of superclass" hd]
			Just sk -> checkKinds hd sk ak
		    mapM_ (addClassDecl ak (Set.single hd) Nothing) cls
		    return $ SubclassDecl cls ak sc qs
		  else do (sk, newSc@(Intersection newSups _)) <- anaClass sc
			  checkKinds hd sk ak
			  mapM_ (addClassDecl ak newSups Nothing) cls
			  return $ SubclassDecl cls ak newSc qs


anaClassDecls (ClassDefn ci k ic ps) =
    do ak <- anaKind k
       (dk, newIc) <- anaClass ic
       checkKinds ci dk ak
       (newKind, _, mDefn) <- addClassDecl ak Set.empty (Just newIc) ci 
       return $ case mDefn of 
           Nothing -> ClassDecl [ci] newKind ps 
	   Just newDefn -> ClassDefn ci newKind newDefn ps

anaClassDecls (DownsetDefn ci v t ps) = 
    do mt <- anaStarType t 
       (newKind, _, mDefn) <- addClassDecl star Set.empty (fmap Downset mt) ci
       return $ case mDefn of 
           Nothing -> ClassDecl [ci] newKind ps 
	   Just newDefn -> case newDefn of
	       Downset newT -> DownsetDefn ci v newT ps
	       _ -> ClassDefn ci newKind newDefn ps

-- ---------------------------------------------------------------------------
-- store class decls
-- ---------------------------------------------------------------------------

-- | store a class map
putClassMap :: ClassMap -> State Env ()
putClassMap ce = do { e <- get; put e { classMap = ce } }

-- | store a class 
addClassDecl :: Kind -> Set.Set ClassId -> Maybe Class 
	     -> ClassId -> State Env (Kind, Set.Set ClassId, Maybe Class)
-- check with merge
addClassDecl kind sups defn ci = 
    if showId ci "" == "Type" then 
       do addDiags [mkDiag Error 
		    "illegal universe class declaration" ci]
          return (kind, Set.empty, Nothing)
    else do
       cMap <- gets classMap
       case Map.lookup ci cMap of
            Nothing -> do putClassMap $ Map.insert ci  
				      newClassInfo { classKind = kind
						   , superClasses = sups
						   , classDefn = defn } cMap
			  return (kind, sups, defn)
	    Just info -> do 
	        addDiags [mkDiag Warning "redeclared class" ci]
		let oldDefn = classDefn info
		    oldSups = superClasses info
		    oldKind = classKind info
                    (ds, newDefn) = case (oldDefn, defn) of 
			 (Nothing, Nothing) -> ([], Nothing)
			 (Just _, Nothing) -> 
			     ([mkDiag Error 
			       "alias class cannot become a real class" ci]
			      , oldDefn)
			 (Nothing, Just _) -> 
			     ([mkDiag Error 
			       "class cannot become an alias class" ci]
			      , Nothing)
			 (Just d1, Just d2) -> 
			     let Result es _ = merge d1 d2 in
				 (map (improveDiag ci) es, oldDefn)
		checkKinds ci kind oldKind
		addDiags ds 
		possSups <- getLegalSuperClasses ci oldSups sups
		let newSups = case newDefn of Just _ -> Set.empty
					      Nothing -> possSups
		putClassMap $ Map.insert ci info 
				      { superClasses = newSups
				      , classDefn = newDefn } cMap
		return (oldKind, newSups, newDefn)

getLegalSuperClasses :: ClassId -> Set.Set ClassId
		     -> Set.Set ClassId -> State Env (Set.Set ClassId)
getLegalSuperClasses ci oldCs ses =
    do ce <- gets classMap
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
