
{- HetCATS/HasCASL/ClassDecl.hs
   $Id$
   Authors: Christian Maeder
   Year:    2003
   
   analyse class decls
-}

module ClassDecl where

import As
import FiniteMap
import Id
import Le
import Data.List
import Data.Maybe
import Control.Monad.State
import Result
import ClassAna

anaClassDecls :: ClassDecl -> State Env ()
anaClassDecls (ClassDecl cls _) = 
    mapM_ (anaClassDecl [] Nothing) cls

anaClassDecls (SubclassDecl _ (Downset _) _) = error "anaClassDecl"
anaClassDecls (SubclassDecl cls sc@(Intersection supcls ps) qs) =
       if null supcls then 
	  do addDiag $ Diag Warning
			  "redundant universe class" 
			 $ if null ps then head qs else head ps
	     mapM_ (anaClassDecl [] Nothing) cls
          else let hd:tl = supcls in 
	      if null $ tl then
		 do cMap <- getClassMap 
		    if null $ anaClassId cMap hd then
		       return () else do  
			  anaClassDecl [] Nothing hd
			  addDiag $ mkDiag Warning 
				      "implicit declaration of superclass" hd
		    mapM_ (anaClassDecl [hd] Nothing) cls
		  else do Intersection newSups _ <- anaClass sc
			  mapM_ (anaClassDecl newSups Nothing) cls

anaClassDecls (ClassDefn ci ic _) =
    do newIc <- anaClass ic
       anaClassDecl [] (Just newIc) ci 

anaClassDecls (DownsetDefn ci _ t _) = 
    do downsetWarning t
       anaClassDecl [] (Just $ Downset t) ci

anaClassDecl :: [ClassId] -> Maybe Class -> ClassId -> State Env ()
anaClassDecl sups defn ci = 
    if showId ci "" == "Type" then 
       addDiag $ Diag Error 
		    "illegal universe class declaration" $ posOfId ci
    else do
       cMap <- getClassMap
       case lookupFM cMap ci of
            Nothing -> putClassMap $ addToFM cMap ci  
		       newClassInfo { superClasses = sups, 
					   classDefn = defn }
	    Just info -> do 
	        addDiag $ mkDiag Warning "redeclared class" ci
		let oldDefn = classDefn info
		    oldSups = superClasses info
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
		      putClassMap $ addToFM cMap ci info 
				      { superClasses = newSups } 

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
