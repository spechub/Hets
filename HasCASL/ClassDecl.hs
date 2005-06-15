{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable 

   analyse class decls
-}

module HasCASL.ClassDecl where

import HasCASL.As
import HasCASL.Le
import HasCASL.ClassAna
import HasCASL.VarDecl
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.Id
import Common.Lib.State
import Common.Result

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
                addDiags $ checkKinds ci kind $ head superClasses
                if kind `elem` superClasses then
                   return () 
                   else if cyclicClassId ci kind then
                   addDiags [mkDiag Error "cyclic class" ci]
                   else putClassMap $ Map.insert ci info 
                                      { classKinds = Set.toList $
                                        mkIntersection 
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
