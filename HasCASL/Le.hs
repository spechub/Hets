
{- HetCATS/HasCASL/Le.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002/2003
   
   abstract syntax after/during static analysis
-}

module HasCASL.Le where

import Common.Id
import HasCASL.As
import Common.Lib.Map
import Data.List
import Control.Monad.State
import Common.Result

-----------------------------------------------------------------------------
-- classInfo
-----------------------------------------------------------------------------

data ClassInfo = ClassInfo { superClasses :: [ClassId]
			   , classDefn :: Maybe Class
			   } deriving (Show, Eq)

newClassInfo :: ClassInfo
newClassInfo = ClassInfo [] Nothing

-----------------------------------------------------------------------------

type ClassMap = Map ClassId ClassInfo

-----------------------------------------------------------------------------
-- typeInfo
-----------------------------------------------------------------------------

data GenKind = Free | Generated | Loose deriving (Show, Eq) 

data TypeDefn = NoTypeDefn
              | Supertype TypeId Type Formula 
	      | DatatypeDefn GenKind -- ...
	      | AliasTypeDefn TypeScheme
	      | TypeVarDefn deriving (Show, Eq)

data TypeInfo = TypeInfo { typeKind :: Kind
			 , otherTypeKinds :: [Kind]
			 , superTypes :: [Type]
			 , typeDefn :: TypeDefn
			 } deriving (Show, Eq)
 
-----------------------------------------------------------------------------

type TypeMap = Map TypeId TypeInfo

-----------------------------------------------------------------------------
-- assumptions
-----------------------------------------------------------------------------

type Assumps = Map Id [TypeScheme]

-----------------------------------------------------------------------------
-- local env
-----------------------------------------------------------------------------

data Env = Env { classMap :: ClassMap
               , typeMap :: TypeMap
	       , assumps :: Assumps
	       , envDiags :: [Diagnosis]
	       } deriving Show

initialEnv :: Env
initialEnv = Env empty empty empty []

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

getTypeMap :: State Env TypeMap
getTypeMap = gets typeMap

putTypeMap :: TypeMap -> State Env ()
putTypeMap tk =  do { e <- get; put e { typeMap = tk } }

getAssumps :: State Env Assumps
getAssumps = gets assumps

putAssumps :: Assumps -> State Env ()
putAssumps as =  do { e <- get; put e { assumps = as } }
