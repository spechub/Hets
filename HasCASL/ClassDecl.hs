
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
import List
import Maybe
import MonadState
import Result
import TypeAna

anaClassDecls :: ClassDecl -> State Env ()
anaClassDecls (ClassDecl cls _) = 
    mapM_ (anaClassDecl [] Nothing) cls

anaClassDecls (SubclassDecl _ (Downset _) _) = error "anaClassDecl"
anaClassDecls (SubclassDecl cls sc@(Intersection supcls ps) _) =
       if null supcls then 
	  do appendDiags [Diag Warning
			  "redundant universe class" 
			 $ head ps ] 
	     mapM_ (anaClassDecl [] Nothing) cls
          else let hd:tl = supcls in 
	      if null $ tl then
		 do cMap <- getClassMap 
		    if null $ anaClassId cMap hd then
		       return () else do  
			  anaClassDecl [] Nothing hd
			  appendDiags [Diag Warning 
				       ("implicit declaration of superclass '"
					++ showId hd "'")
				      $ posOfId hd]
		    mapM_ (anaClassDecl [hd] Nothing) cls
		  else do Intersection newSups _ <- anaClass sc
			  mapM_ (anaClassDecl newSups Nothing) cls

anaClassDecls (ClassDefn ci ic _) =
    anaClassDecl [] (Just ic) ci 

anaClassDecls (DownsetDefn ci _ t _) = 
    do newT <- anaType t 
       anaClassDecl [] (Just $ Downset t) ci

anaClassDecl :: [ClassId] -> Maybe Class -> ClassId -> State Env ()
anaClassDecl sups defn ci = 
    if showId ci "" == "Type" then 
       appendDiags [Diag Error 
		    "illegal universe class declaration" (posOfId ci)]
    else do
       cMap <- getClassMap
       case lookupFM cMap ci of
            Nothing -> putClassMap $ addToFM cMap ci $ newClassInfo ci
	    Just _ -> appendDiags [Diag Warning 
				   ("redeclared class '"
				    ++ showId ci "'") 
				  $ posOfId ci]
       if null sups && isNothing defn then return ()
	  else do 
	       cMap2 <- getClassMap			     
	       let info = fromJust $ lookupFM cMap2 ci
	       newSups <- getLegalSuperClasses ci (superClasses info) sups
	       newDefn <- mergeDefns ci (classDefn info) defn
	       putClassMap $ addToFM cMap2 ci info 
		       { superClasses = newSups, 
		         classDefn = newDefn }

getLegalSuperClasses :: ClassId -> [ClassId] 
		     -> [ClassId] -> State Env [ClassId]
getLegalSuperClasses ci oldCs cs =
    do ce <- getClassMap
       let scs = zip (map (allSuperClasses ce) cs) cs
	   (scycs, sOk) = partition ((ci `elem`) . fst) scs
	   defCs = map snd sOk
	   newCs = nub $ defCs ++ oldCs
	   cycles = map snd scycs
	   dubs = filter (`elem` allSuperClasses ce ci) defCs
	   in do if null cycles then return ()
		    else appendDiags 
			     [Diag Error 
			      ("cyclic class relation via '"
			       ++ showClassList cycles "'")
			     $ posOfId (head cycles)]
		 if null dubs then return ()
		    else appendDiags 
			     [Diag Warning 
			      ("already known as super class '"
			       ++ showClassList dubs "'")
			     $ posOfId (head dubs)]
		 return newCs

showClassList :: [ClassId] -> ShowS
showClassList is = showParen (length is > 1)
		   $ showSepList ("," ++) showId is

mergeDefns :: ClassId -> Maybe Class -> Maybe Class -> State Env (Maybe Class) 
mergeDefns _ Nothing Nothing = return Nothing

mergeDefns ci c1@(Just (Downset oldT)) c2@(Just (Downset t)) =
    if eqType oldT t then return c2
       else do wrongClassDecl ci
	       return c1

mergeDefns ci c1@(Just (Intersection oldIs _)) c2@(Just (Intersection is _)) =
    do cMap <- getClassMap
       if sort (resolveClassSyns cMap oldIs) ==
	  sort (resolveClassSyns cMap is)
	  then return c2
	  else do wrongClassDecl ci
	          return c1

mergeDefns ci c@(Just _) (Just _) =
    do wrongClassDecl ci
       return c

mergeDefns _ c Nothing = return c
mergeDefns ci Nothing (Just (Intersection is ps)) = 
    do cMap <- getClassMap
       js <- getLegalSuperClasses ci [] is
       return $ Just $ Intersection js ps

mergeDefns ci Nothing c@(Just _) = 
    do cMap <- getClassMap
       let sups = delete ci $ allSuperClasses cMap ci 
	   sDefns = map (classDefn . fromJust . lookupFM cMap) sups 
	   jDefns = filter ( \ x -> case x of 
			     Just (Downset _) -> True
			     _ -> False ) sDefns
       if null jDefns then return ()
	  else appendDiags [Diag Warning 
			    ("downset definition may conflict " 
			    ++ "with those of superclasses")
			    $ posOfId ci]
       return c


wrongClassDecl :: ClassId -> State Env ()
wrongClassDecl ci =
    appendDiags [Diag Error 
		 ("inconsistent redefinition of '" ++ showId ci "'")
		 $ posOfId ci]
