
{- HetCATS/HasCASL/Le.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002/2003
   
   abstract syntax after/during static analysis
-}

module Le where

import Id
import As
import FiniteMap
import List
import MonadState
import Result

-----------------------------------------------------------------------------
-- classInfo
-----------------------------------------------------------------------------

data ClassInfo = ClassInfo { superClasses :: [ClassId]
			   , classDefn :: Maybe Class
			   } deriving (Show, Eq)

newClassInfo :: ClassInfo
newClassInfo = ClassInfo [] Nothing

-----------------------------------------------------------------------------

type ClassMap = FiniteMap ClassId ClassInfo

-----------------------------------------------------------------------------
-- typeInfo
-----------------------------------------------------------------------------

data GenKind = Free | Generated | Loose deriving (Show, Eq) 

data TypeDefn = NoTypeDefn
              | SubTypeDefn TypeId Type Formula 
	      | DatatypeDefn GenKind -- ...
	      | AliasTypeDefn TypeScheme
	      | TypeVarDefn deriving (Show, Eq)

data TypeInfo = TypeInfo { typeKind :: Kind
			 , otherTypeKinds :: [Kind]
			 , superTypes :: [Type]
			 , typeDefn :: TypeDefn
			 } deriving (Show, Eq)
 
-----------------------------------------------------------------------------

type TypeKinds = FiniteMap TypeId TypeInfo

-----------------------------------------------------------------------------
-- assumptions
-----------------------------------------------------------------------------

type Assumps = FiniteMap Id [TypeScheme]

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

addDiag :: Diagnosis -> State Env ()
addDiag d = appendDiags [d]

indent :: Int -> ShowS -> ShowS
indent i s = showString $ concat $ 
	     intersperse ('\n' : replicate i ' ') (lines $ s "")

-- ---------------------------------------------------------------------

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
