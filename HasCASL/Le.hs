
{- HetCATS/HasCASL/Le.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002/2003
   
   abstract syntax after/during static analysis
-}

module HasCASL.Le where

import HasCASL.As
import Common.Lib.Map as Map
import Common.Lib.Set as Set
import Common.Result
import Common.GlobalAnnotations
import Common.Named

-----------------------------------------------------------------------------
-- classInfo
-----------------------------------------------------------------------------

data ClassInfo = ClassInfo { superClasses :: Set ClassId
                           , classKind :: Kind
			   , classDefn :: Maybe Class
			   } deriving (Show, Eq)

newClassInfo :: ClassInfo
newClassInfo = ClassInfo Set.empty star Nothing

-----------------------------------------------------------------------------

type ClassMap = Map ClassId ClassInfo

-----------------------------------------------------------------------------
-- typeInfo
-----------------------------------------------------------------------------

data GenKind = Free | Generated | Loose deriving (Show, Eq) 

data AltDefn = Construct UninstOpId [Type] Partiality [Selector] 
               -- argument types
	       deriving (Show, Eq) 

data Selector = Select UninstOpId Type Partiality -- only result type
		deriving (Show, Eq) 

data TypeDefn = NoTypeDefn
              | Supertype Vars Type Formula 
	      | DatatypeDefn GenKind [TypeArg] [AltDefn]
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

data OpInfo = OpInfo { opType :: TypeScheme
		     , opAttrs :: [OpAttr]
		     , opDefn :: OpDefn
		     } deriving (Show, Eq)

data ConstrInfo = ConstrInfo { constrId :: UninstOpId
			     , constrType :: TypeScheme 
			     } deriving (Show, Eq)

data OpDefn = NoOpDefn
	    | ConstructData TypeId     -- target type
	    | SelectData [ConstrInfo] TypeId   -- constructors of source type
	    | Definition Term            
	    | VarDefn deriving (Show, Eq)


newtype OpInfos = OpInfos { opInfos :: [OpInfo] } deriving (Show, Eq)

type Assumps = Map UninstOpId OpInfos

-----------------------------------------------------------------------------
-- local env
-----------------------------------------------------------------------------

data Env = Env { classMap :: ClassMap
               , typeMap :: TypeMap
	       , assumps :: Assumps
	       , sentences :: [Named Formula]	 
               , globalAnnos :: GlobalAnnos
	       , envDiags :: [Diagnosis]
	       , counter :: Int
	       } deriving Show

instance Eq Env where
    Env c1 t1 a1 s1 _ _ _ == Env c2 t2 a2 s2 _ _ _ = 
	(c1, t1, a1, s1) == (c2, t2, a2, s2)

initialEnv :: Env
initialEnv = Env Map.empty Map.empty Map.empty [] emptyGlobalAnnos [] 1

