
{- HetCATS/HasCASL/ClassDecl.hs
   $Id$
   Authors: Christian Maeder
   Year:    2003
   
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
import HasCASL.Reader

addDiags :: (Env -> b) ->  ReadR b a -> State Env (Maybe a) 
addDiags f r = do Result ds m <- toState f r 
		  appendDiags ds
		  return m
		  

anaClassDecls :: ClassDecl -> State Env ()
anaClassDecls (ClassDecl cls k _) = 
    do Just ak <- addDiags classMap $ anaKind k
       mapM_ (anaClassDecl ak Set.empty Nothing) cls

anaClassDecls (SubclassDecl _ _ (Downset _) _) = error "anaClassDecl"
anaClassDecls (SubclassDecl cls k sc@(Intersection supcls ps) qs) =
    do Just ak <- addDiags classMap $ anaKind k
       cMap <- gets classMap 
       if Set.isEmpty supcls then 
	  do addDiag $ Diag Warning
			  "redundant universe class" 
			 $ if null ps then head qs else head ps
	     mapM_ (anaClassDecl ak supcls Nothing) cls
          else let (hd, tl) = Set.deleteFindMin supcls in 
	      if Set.isEmpty tl then
		 do if isJust $ anaClassId cMap hd then
		       return () else do  
			  anaClassDecl ak tl Nothing hd
			  addDiag $ mkDiag Warning 
				      "implicit declaration of superclass" hd
		    mapM_ (anaClassDecl ak (Set.single hd) Nothing) cls
		  else do Just (sk, Intersection newSups _) <- 
			      addDiags classMap $ anaClass sc
			  appendDiags $ checkKinds cMap (posOfId hd) sk ak
			  mapM_ (anaClassDecl ak newSups Nothing) cls

anaClassDecls (ClassDefn ci k ic _) =
    do Just ak <- addDiags classMap $ anaKind k
       Just (dk, newIc) <- addDiags classMap $ anaClass ic
       cMap <- gets classMap
       appendDiags $ checkKinds cMap (posOfId ci) dk ak
       anaClassDecl ak Set.empty (Just newIc) ci 

anaClassDecls (DownsetDefn ci _ t _) = 
    do addDiag $ downsetWarning t
       anaClassDecl star Set.empty (Just $ Downset t) ci

anaClassDecl :: Kind -> Set.Set ClassId -> Maybe Class 
	     -> ClassId -> State Env ()
anaClassDecl kind sups defn ci = 
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
		appendDiags $ checkKinds cMap (posOfId ci) kind oldKind
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
