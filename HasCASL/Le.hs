
{- HetCATS/HasCASL/Le.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002/2003
   
   abstract syntax after/during static analysis
-}

module Le where

import Id
import As
import AsUtils
import MonadState
import FiniteMap
import List
import Result
import Set

data ClassInfo = ClassInfo { classId :: ClassName
			   , superClasses :: [ClassName]
			   , classDefn :: Class
			   , instances :: [Qual Pred]
			   } deriving (Show, Eq)

newClassInfo :: ClassName -> ClassInfo
newClassInfo cid = ClassInfo cid [] (Intersection [] []) []

-----------------------------------------------------------------------------

type ClassEnv = FiniteMap ClassName ClassInfo

-- transitiv super classes 
-- PRE: all superclasses and defns must be defined in ClassEnv
-- and there must be no cycle!
allSuperClasses :: ClassEnv -> ClassName -> [ClassName]
allSuperClasses ce ci = 
    case lookupFM ce ci of 
    Just info -> nub $
		      ci: concatMap (allSuperClasses ce) (iclass $ 
							  classDefn info) 
		      ++  concatMap (allSuperClasses ce) (superClasses info)
    Nothing -> error "allSuperClasses"

defCEntry :: ClassEnv -> ClassName  -> [ClassName] -> Class -> ClassEnv
defCEntry ce cid sups defn = addToFM ce cid 
			   (newClassInfo cid) { superClasses = sups
					      , classDefn = defn } 

-----------------------------------------------------------------------------
-- assumptions
-----------------------------------------------------------------------------

type Assumps = FiniteMap Id [TypeScheme]

type TypeKinds = FiniteMap TypeName Kind

-----------------------------------------------------------------------------
-- local env
-----------------------------------------------------------------------------

data Env = Env { classEnv :: ClassEnv
               , typeKinds :: TypeKinds
	       , typeVars :: Set TypeName
	       , assumps :: Assumps
	       , envDiags :: [Diagnosis]
	       } deriving Show

initialEnv :: Env
initialEnv = Env emptyFM emptyFM emptySet emptyFM []

appendDiags :: [Diagnosis] -> State Env ()
appendDiags ds =
    if null ds then return () else
    do e <- get
       put $ e {envDiags = ds ++ envDiags e}


getClassEnv :: State Env ClassEnv
getClassEnv = gets classEnv

putClassEnv :: ClassEnv -> State Env ()
putClassEnv ce = do { e <- get; put e { classEnv = ce } }

getTypeKinds :: State Env TypeKinds
getTypeKinds = gets typeKinds

putTypeKinds :: TypeKinds -> State Env ()
putTypeKinds tk =  do { e <- get; put e { typeKinds = tk } }

getAssumps :: State Env Assumps
getAssumps = gets assumps

putAssumps :: Assumps -> State Env ()
putAssumps as =  do { e <- get; put e { assumps = as } }

getTypeVars :: State Env (Set TypeName)
getTypeVars = gets typeVars

putTypeVars :: (Set TypeName) -> State Env ()
putTypeVars ts =  do { e <- get; put e { typeVars = ts } }

addTypeVar :: TypeName -> State Env ()
addTypeVar t = do ts <- getTypeVars 
		  putTypeVars $ addToSet ts t
