
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
import Data.List
import HasCASL.Reader
import Common.Lib.State
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

data AltDefn = Construct UninstOpId TypeScheme [Selector] 
	       deriving (Show, Eq) 

data Selector = Select UninstOpId TypeScheme 
		deriving (Show, Eq) 

data TypeDefn = NoTypeDefn
              | Supertype Vars Type Formula 
	      | DatatypeDefn GenKind [AltDefn]
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

data OpDefn = NoOpDefn
	    | ConstructData TypeId     -- target type
	    | SelectData [UninstOpId] TypeId   -- constructors of source type
	    | Definition Term            
	    | VarDefn deriving (Show, Eq)


type Assumps = Map UninstOpId [OpInfo]

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

appendDiags :: [Diagnosis] -> State Env ()
appendDiags ds =
    if null ds then return () else
    do e <- get
       put $ e {envDiags = ds ++ envDiags e}

addDiag :: Diagnosis -> State Env ()
addDiag d = appendDiags [d]

putCounter :: Int -> State Env ()
putCounter i = do { e <- get; put e { counter = i } }

putClassMap :: ClassMap -> State Env ()
putClassMap ce = do { e <- get; put e { classMap = ce } }

putTypeMap :: TypeMap -> State Env ()
putTypeMap tk =  do { e <- get; put e { typeMap = tk } }

putAssumps :: Assumps -> State Env ()
putAssumps as =  do { e <- get; put e { assumps = as } }

-- ---------------------------------------------------------------------

toMaybeState :: (Env -> r) -> ReadR r a -> State Env (Maybe a) 
toMaybeState f r = do Result ds m <- toResultState f r 
		      appendDiags ds 
		      return m

toState :: a -> (Env -> r) -> ReadR r a -> State Env a
toState d f r = do m <- toMaybeState f r
		   return $ case m of Nothing -> d
				      Just a -> a

-- ---------------------------------------------------------------------
indent :: Int -> ShowS -> ShowS
indent i s = showString $ concat $ 
	     intersperse ('\n' : replicate i ' ') (lines $ s "")

-- ---------------------------------------------------------------------

