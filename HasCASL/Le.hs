{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 

   abstract syntax during static analysis
-}

module HasCASL.Le where

import HasCASL.As
import HasCASL.AsToIds
import Common.Lib.Map as Map
import Common.Result
import Common.Lib.State
import Common.Named
import Common.Id

-----------------------------------------------------------------------------
-- classInfo
-----------------------------------------------------------------------------

data ClassInfo = ClassInfo { classKinds :: [Kind] -- superKinds
			   } deriving (Show, Eq)

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
              | PreDatatype     -- auxiliary entry for DatatypeDefn
              | Supertype Vars TypeScheme Term 
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

data OpDefn = NoOpDefn OpBrand
	    | ConstructData TypeId     -- target type
	    | SelectData [ConstrInfo] TypeId   -- constructors of source type
	    | Definition OpBrand Term            
	    | VarDefn deriving (Show, Eq)

isVarDefn :: OpInfo -> Bool
isVarDefn o = case opDefn o of 
	      VarDefn -> True
	      _       -> False 

data OpInfos = OpInfos { opInfos :: [OpInfo] } deriving (Show, Eq)

type Assumps = Map UninstOpId OpInfos

-----------------------------------------------------------------------------
-- local env
-----------------------------------------------------------------------------

data Env = Env { classMap :: ClassMap
               , typeMap :: TypeMap
	       , assumps :: Assumps
	       , sentences :: [Named Term]	 
	       , envDiags :: [Diagnosis]
	       , mixRules :: [(Id, (), [Token])]
	       , counter :: Int
	       } deriving (Show, Eq)

initialEnv :: Env
initialEnv = Env Map.empty Map.empty Map.empty [] [] [] 1

-- | add diagnostic messages 
addDiags :: [Diagnosis] -> State Env ()
addDiags ds =
    do e <- get
       put $ e {envDiags = ds ++ envDiags e}

