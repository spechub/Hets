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
import Common.Id
import HasCASL.Le
import Data.List
import Data.Maybe
import Common.Lib.State
import Common.Result
import HasCASL.ClassAna
import HasCASL.TypeAna

-- ---------------------------------------------------------------------------
-- analyse class decls
-- ---------------------------------------------------------------------------

anaClassDecls :: ClassDecl -> State Env ClassDecl
anaClassDecls (ClassDecl cls k ps) = 
    do ak <- anaKind k
       mapM_ (addClassDecl ak) cls
       return $ ClassDecl cls ak ps

-- ---------------------------------------------------------------------------
-- store class decls
-- ---------------------------------------------------------------------------

-- | store a class map
putClassMap :: ClassMap -> State Env ()
putClassMap ce = do { e <- get; put e { classMap = ce } }

-- | store a class 
addClassDecl :: Kind -> ClassId 
	     -> State Env ()
-- check with merge
addClassDecl kind ci = 
    if showId ci "" == "Type" then 
       do addDiags [mkDiag Error 
		    "illegal universe class declaration" ci]
    else do
       cMap <- gets classMap
       case Map.lookup ci cMap of
            Nothing -> do putClassMap $ Map.insert ci  
			      ClassInfo { classKinds = [kind] } cMap
	    Just info -> do 
		addDiags [mkDiag Warning "redeclared class" ci]
		let superClasses = classKinds info
		checkKinds ci kind $ head superClasses
	        if kind `elem` superClasses then
		   return () 
		   else if cyclicClassId ci kind then
		   addDiags [mkDiag Error "cyclic class" ci]
		   else putClassMap $ Map.insert ci info 
				      { classKinds = mkIntersection 
					(kind:superClasses) } cMap

-- cycle check missing

showClassList :: [ClassId] -> ShowS
showClassList is = showParen (not $ isSingle is)
		   $ showSepList ("," ++) showId is

wrongClassDecl :: ClassId -> [Diagnosis]
wrongClassDecl ci =
    [Diag Error 
		 ("inconsistent redefinition of '" ++ showId ci "'")
		 $ posOfId ci]
