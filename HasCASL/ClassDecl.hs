{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003-2005
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
import Common.Id
import Common.Lib.State
import Common.Result

-- ---------------------------------------------------------------------------
-- analyse class decls
-- ---------------------------------------------------------------------------

anaClassDecls :: ClassDecl -> State Env ClassDecl
anaClassDecls (ClassDecl cls k ps) = 
    do cm <- gets classMap 
       let Result ds (Just rk) = anaKindM k cm
       addDiags ds 
       let ak = if null ds then k else rk
       mapM_ (addClassDecl ak) cls
       return $ ClassDecl cls ak ps

-- ---------------------------------------------------------------------------
-- store class decls
-- ---------------------------------------------------------------------------

-- | store a class map
putClassMap :: ClassMap -> State Env ()
putClassMap ce = do { e <- get; put e { classMap = ce } }

-- | store a class 
addClassDecl :: Kind -> ClassId -> State Env ()
-- check with merge
addClassDecl kind ci = 
    if showId ci "" == "Type" then 
       do addDiags [mkDiag Warning 
                    "void universe class declaration" ci]
    else do
       rk <- anaKind kind
       cm <- gets classMap
       case Map.lookup ci cm of
            Nothing -> do putClassMap $ Map.insert ci  
                              (ClassInfo rk [kind]) cm
            Just (ClassInfo ork superClasses) -> do 
                let ds = checkKinds ci rk ork
                addDiags ds
                if null ds then 
                   if cyclicClassId cm ci kind then
                   addDiags [mkDiag Error "cyclic class" ci]
                   else if any (\ k -> lesserKind cm k kind) superClasses 
                        then addDiags [mkDiag Warning "unchanged class" ci]
                        else do addDiags [mkDiag Hint 
                                         "refined class" ci]
                                putClassMap $ Map.insert ci 
                                    (ClassInfo ork $ keepMinKinds cm $ 
                                               kind : superClasses) cm
                   else return ()

showClassList :: [ClassId] -> ShowS
showClassList is = showParen (not $ isSingle is)
                   $ showSepList ("," ++) showId is

wrongClassDecl :: ClassId -> [Diagnosis]
wrongClassDecl ci =
    [Diag Error 
                 ("inconsistent redefinition of '" ++ showId ci "'")
                 $ posOfId ci]
