
{- HetCATS/HasCASL/ClassDecl.hs
   $Id$
   Authors: Christian Maeder
   Year:    2003
   
   analyse class decls
-}

module HasCASL.ClassDecl where

import HasCASL.As
import qualified Common.Lib.Map as Map
import Common.Id
import HasCASL.Le
import Data.List
import Data.Maybe
import Control.Monad.State
import Common.Result
import HasCASL.ClassAna

anaClassDecls :: ClassDecl -> State Env ()
anaClassDecls (ClassDecl cls k _) = 
    do ak <- anaKind k
       mapM_ (anaClassDecl ak [] Nothing) cls

anaClassDecls (SubclassDecl _ _ (Downset _) _) = error "anaClassDecl"
anaClassDecls (SubclassDecl cls k sc@(Intersection supcls ps) qs) =
    do ak <- anaKind k
       if null supcls then 
	  do addDiag $ Diag Warning
			  "redundant universe class" 
			 $ if null ps then head qs else head ps
	     mapM_ (anaClassDecl ak [] Nothing) cls
          else let hd:tl = supcls in 
	      if null $ tl then
		 do cMap <- getClassMap 
		    if isJust $ anaClassId cMap hd then
		       return () else do  
			  anaClassDecl ak [] Nothing hd
			  addDiag $ mkDiag Warning 
				      "implicit declaration of superclass" hd
		    mapM_ (anaClassDecl ak [hd] Nothing) cls
		  else do (sk, Intersection newSups _) <- anaClass sc
			  checkKinds (posOfId hd) sk ak
			  mapM_ (anaClassDecl ak newSups Nothing) cls

anaClassDecls (ClassDefn ci k ic _) =
    do ak <- anaKind k
       (dk, newIc) <- anaClass ic
       checkKinds (posOfId ci) dk ak
       anaClassDecl ak [] (Just newIc) ci 

anaClassDecls (DownsetDefn ci _ t _) = 
    do downsetWarning t
       anaClassDecl star [] (Just $ Downset t) ci

anaClassDecl :: Kind -> [ClassId] -> Maybe Class -> ClassId -> State Env ()
anaClassDecl kind sups defn ci = 
    if showId ci "" == "Type" then 
       addDiag $ Diag Error 
		    "illegal universe class declaration" $ posOfId ci
    else do
       cMap <- getClassMap
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
		checkKinds (posOfId ci) kind oldKind
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

getLegalSuperClasses :: ClassMap -> ClassId -> [ClassId] 
		     -> [ClassId] -> State Env [ClassId]
getLegalSuperClasses ce ci oldCs cs =
       let scs = zip (map (allSuperClasses ce) cs) cs
	   (scycs, sOk) = partition ((ci `elem`) . fst) scs
	   defCs = map snd sOk
	   newCs = nub $ defCs ++ oldCs
	   cycles = map snd scycs
	   dubs = filter (`elem` allSuperClasses ce ci) defCs
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

mergeDefns :: ClassId -> Class -> Class -> [Diagnosis]

mergeDefns ci (Downset oldT) (Downset t) =
    if oldT == t then [] else wrongClassDecl ci

mergeDefns ci (Intersection oldIs _) (Intersection is _) =
       if sort (nub oldIs) == sort (nub is) then []
	  else wrongClassDecl ci

mergeDefns ci _ _ = wrongClassDecl ci

wrongClassDecl :: ClassId -> [Diagnosis]
wrongClassDecl ci =
    [Diag Error 
		 ("inconsistent redefinition of '" ++ showId ci "'")
		 $ posOfId ci]
