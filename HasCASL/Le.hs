{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 

   abstract syntax during static analysis
-}

module HasCASL.Le where

import HasCASL.As
import Common.Lib.Map as Map
import Common.Lib.Set as Set
import Common.Result
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
              | Supertype Vars Type Term 
	      | DatatypeDefn GenKind [TypeArg] [AltDefn]
	      | AliasTypeDefn TypeScheme
	      | TypeVarDefn deriving (Show, Eq)

data TypeInfo = TypeInfo { typeKind :: Kind
			 , otherTypeKinds :: [Kind]
			 , superTypes :: [Type]
			 , typeDefn :: TypeDefn
			 } deriving (Show, Eq)

isTypeVarDefn :: TypeInfo -> Bool
isTypeVarDefn t = case typeDefn t of
		  TypeVarDefn -> True
		  _           -> False
 
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

isVarDefn :: OpInfo -> Bool
isVarDefn o = case opDefn o of 
	      VarDefn -> True
	      _       -> False 

newtype OpInfos = OpInfos { opInfos :: [OpInfo] } deriving (Show, Eq)

type Assumps = Map UninstOpId OpInfos

-----------------------------------------------------------------------------
-- local env
-----------------------------------------------------------------------------

data Env = Env { classMap :: ClassMap
               , typeMap :: TypeMap
	       , assumps :: Assumps
	       , sentences :: [Named Term]	 
	       , envDiags :: [Diagnosis]
	       , counter :: Int
	       } deriving (Show, Eq)

initialEnv :: Env
initialEnv = Env Map.empty Map.empty Map.empty [] [] 1

