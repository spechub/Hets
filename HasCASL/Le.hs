
{- HetCATS/HasCASL/Le.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002/2003
   
   abstract syntax after/during static analysis
-}

module Le where

import Id
import As
import MonadState
import FiniteMap
import List
import Result

data ClassInfo = ClassInfo { classId :: ClassId
			   , superClasses :: [ClassId]
			   , classDefn :: Maybe Class
			   , instances :: [Qual Pred]
			   } deriving (Show, Eq)

newClassInfo :: ClassId -> ClassInfo
newClassInfo cid = ClassInfo cid [] Nothing []

-----------------------------------------------------------------------------

type ClassMap = FiniteMap ClassId ClassInfo

-----------------------------------------------------------------------------
-- assumptions
-----------------------------------------------------------------------------

type Assumps = FiniteMap Id [TypeScheme]

type TypeKinds = FiniteMap TypeId [Kind]

-----------------------------------------------------------------------------
-- local env
-----------------------------------------------------------------------------

data Env = Env { classMap :: ClassMap
               , typeKinds :: TypeKinds
	       , typeVars :: [TypeId]
	       , assumps :: Assumps
	       , envDiags :: [Diagnosis]
	       } deriving Show

initialEnv :: Env
initialEnv = Env emptyFM emptyFM [] emptyFM []

appendDiags :: [Diagnosis] -> State Env ()
appendDiags ds =
    if null ds then return () else
    do e <- get
       put $ e {envDiags = ds ++ envDiags e}

getClassMap :: State Env ClassMap
getClassMap = gets classMap

putClassMap :: ClassMap -> State Env ()
putClassMap ce = do { e <- get; put e { classMap = ce } }

getTypeKinds :: State Env TypeKinds
getTypeKinds = gets typeKinds

putTypeKinds :: TypeKinds -> State Env ()
putTypeKinds tk =  do { e <- get; put e { typeKinds = tk } }

getAssumps :: State Env Assumps
getAssumps = gets assumps

putAssumps :: Assumps -> State Env ()
putAssumps as =  do { e <- get; put e { assumps = as } }

getTypeVars :: State Env [TypeId]
getTypeVars = gets typeVars

putTypeVars :: [TypeId] -> State Env ()
putTypeVars ts =  do { e <- get; put e { typeVars = ts } }

addTypeVar :: TypeId -> State Env ()
addTypeVar t = do ts <- getTypeVars
		  if t `elem` ts then return ()
		     else putTypeVars $ insert t ts
