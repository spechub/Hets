
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
			   , classDefn :: Class
			   , instances :: [Qual Pred]
			   } deriving (Show, Eq)

newClassInfo :: ClassId -> ClassInfo
newClassInfo cid = ClassInfo cid [] (Intersection [] []) []

-----------------------------------------------------------------------------

type ClassMap = FiniteMap ClassId ClassInfo

-- transitiv super classes 
-- PRE: all superclasses and defns must be defined in ClassEnv
-- and there must be no cycle!
allSuperClasses :: ClassMap -> ClassId -> [ClassId]
allSuperClasses ce ci = 
    case lookupFM ce ci of 
    Just info -> nub $
		      ci: concatMap (allSuperClasses ce) (iclass $ 
							  classDefn info) 
		      ++  concatMap (allSuperClasses ce) (superClasses info)
    Nothing -> error "allSuperClasses"

defCEntry :: ClassMap -> ClassId  -> [ClassId] -> Class -> ClassMap
defCEntry ce cid sups defn = addToFM ce cid 
			   (newClassInfo cid) { superClasses = sups
					      , classDefn = defn } 

-----------------------------------------------------------------------------
-- assumptions
-----------------------------------------------------------------------------

type Assumps = FiniteMap Id [TypeScheme]

type TypeKinds = FiniteMap TypeId [Kind]

type ClassSyns = FiniteMap ClassId [ClassId]

-----------------------------------------------------------------------------
-- local env
-----------------------------------------------------------------------------

data Env = Env { classMap :: ClassMap
	       , classSyns :: ClassSyns
               , typeKinds :: TypeKinds
	       , typeVars :: [TypeId]
	       , assumps :: Assumps
	       , envDiags :: [Diagnosis]
	       } deriving Show

initialEnv :: Env
initialEnv = Env emptyFM emptyFM emptyFM [] emptyFM []

appendDiags :: [Diagnosis] -> State Env ()
appendDiags ds =
    if null ds then return () else
    do e <- get
       put $ e {envDiags = ds ++ envDiags e}

getClassMap :: State Env ClassMap
getClassMap = gets classMap

putClassMap :: ClassMap -> State Env ()
putClassMap ce = do { e <- get; put e { classMap = ce } }

getClassSyns :: State Env ClassSyns
getClassSyns = gets classSyns

getClassEnv :: State Env (ClassMap, ClassSyns)
getClassEnv = do cMap <- getClassMap
		 cSyns <- getClassSyns
		 return (cMap, cSyns)

putClassSyns :: ClassSyns -> State Env ()
putClassSyns ce = do { e <- get; put e { classSyns = ce } }

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
		  putTypeVars $ insert t ts
