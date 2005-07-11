{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable 

abstract syntax during static analysis
-}

module HasCASL.Le where

import HasCASL.As
import HasCASL.AsUtils
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.Result(Diagnosis)
import Common.Id
import Common.AS_Annotation(Named)

-----------------------------------------------------------------------------
-- classInfo
-----------------------------------------------------------------------------

data ClassInfo = ClassInfo { rawKind :: RawKind
                           , classKinds :: [Kind] -- superKinds
                           } deriving (Show, Eq)

-----------------------------------------------------------------------------

type ClassMap = Map.Map ClassId ClassInfo

-----------------------------------------------------------------------------
-- typeInfo
-----------------------------------------------------------------------------

data GenKind = Free | Generated | Loose deriving (Show, Eq, Ord) 

data AltDefn = Construct (Maybe UninstOpId) [Type] Partiality [[Selector]] 
               -- only argument types
               deriving (Show, Eq, Ord) 

data Selector = Select (Maybe UninstOpId) Type Partiality -- only result type
                deriving (Show, Eq, Ord) 

type IdMap = Map.Map TypeId TypeId

mapType :: IdMap -> Type -> Type
mapType m ty = if Map.null m then ty else 
              rename ( \ i k n ->
               let t = TypeName i k n in
               if n == 0 then 
                  case Map.lookup i m of
                  Just j -> TypeName j k 0
                  _ -> t
               else t) ty

data DataEntry = DataEntry IdMap TypeId GenKind [TypeArg] [AltDefn]
                  deriving (Show, Eq, Ord)

data TypeDefn = NoTypeDefn
              | PreDatatype     -- auxiliary entry for DatatypeDefn
              | Supertype Vars TypeScheme Term 
              | DatatypeDefn DataEntry
              | AliasTypeDefn TypeScheme
                deriving (Show, Eq)

data TypeVarDefn = TypeVarDefn RawKind VarKind Int deriving Show

data TypeInfo = TypeInfo { typeKind :: RawKind
                         , otherTypeKinds :: [Kind]
                         , superTypes :: [Type]
                         , typeDefn :: TypeDefn
                         } deriving (Show, Eq)

starTypeInfo :: TypeInfo
starTypeInfo = TypeInfo star [star] [] NoTypeDefn

data Sentence = Formula Term
              | DatatypeSen [DataEntry]
              | ProgEqSen UninstOpId TypeScheme ProgEq
                deriving (Show, Eq, Ord)
 
-----------------------------------------------------------------------------

type TypeMap = Map.Map TypeId TypeInfo

type LocalTypeVars = Map.Map TypeId TypeVarDefn

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
              deriving (Show, Eq)

data VarDefn = VarDefn Type deriving Show

isConstructor :: OpInfo -> Bool
isConstructor o = case opDefn o of
                    ConstructData _ -> True
                    _ -> False

data OpInfos = OpInfos { opInfos :: [OpInfo] } deriving (Show, Eq)

type Assumps = Map.Map UninstOpId OpInfos

-----------------------------------------------------------------------------
-- local env
-----------------------------------------------------------------------------

type PrecMap = (Map.Map Id Int, Int, Int)

data Env = Env { classMap :: ClassMap
               , typeMap :: TypeMap
               , localTypeVars :: LocalTypeVars
               , assumps :: Assumps
               , localVars :: Map.Map Id VarDefn
               , sentences :: [Named Sentence]       
               , envDiags :: [Diagnosis]
               , preIds :: (PrecMap, Set.Set Id)
               , counter :: Int
               } deriving Show

initialEnv :: Env
initialEnv = Env Map.empty Map.empty Map.empty Map.empty Map.empty [] [] 
             ((Map.empty, 0, 0), Set.empty) 1

-----------------------------------------------------------------------------
-- symbol stuff
-----------------------------------------------------------------------------

data SymbolType = OpAsItemType TypeScheme
                | TypeAsItemType Kind
                | ClassAsItemType Kind
                  deriving (Show, Eq, Ord)

data Symbol = Symbol {symName :: Id, symType :: SymbolType, symEnv :: Env} 
              deriving Show

instance Eq Symbol where
    s1 == s2 = (symName s1, symType s1) == (symName s2, symType s2)

instance Ord Symbol where
    s1 <= s2 = (symName s1, symType s1) <= (symName s2, symType s2)


type SymbolMap = Map.Map Symbol Symbol 
type SymbolSet = Set.Set Symbol 

idToTypeSymbol :: Env -> Id -> Kind -> Symbol
idToTypeSymbol e idt k = Symbol idt (TypeAsItemType k) e

idToClassSymbol :: Env -> Id -> Kind -> Symbol
idToClassSymbol e idt k = Symbol idt (ClassAsItemType k) e

idToOpSymbol :: Env -> Id -> TypeScheme -> Symbol
idToOpSymbol e idt typ = Symbol idt (OpAsItemType typ) e

-- note that the type of a qualified raw symbol is not analysed!
data RawSymbol = AnID Id | AKindedId SymbKind Id 
               | AQualId Id SymbolType
               | ASymbol Symbol
                 deriving (Show, Eq, Ord)

type RawSymbolMap = Map.Map RawSymbol RawSymbol

idToRaw :: Id -> RawSymbol
idToRaw x = AnID x

rawSymName :: RawSymbol -> Id
rawSymName (AnID i) = i
rawSymName (AKindedId _ i) = i
rawSymName (AQualId i _) = i
rawSymName (ASymbol s) = symName s

symbTypeToKind :: SymbolType -> SymbKind
symbTypeToKind (OpAsItemType _)    = SK_op
symbTypeToKind (TypeAsItemType _)  = SK_type
symbTypeToKind (ClassAsItemType _) = SK_class

symbolToRaw :: Symbol -> RawSymbol
symbolToRaw sym = ASymbol sym

symbKindToRaw :: SymbKind -> Id -> RawSymbol
symbKindToRaw Implicit = AnID 
symbKindToRaw sk = AKindedId $ case sk of 
                   SK_pred -> SK_op
                   SK_fun -> SK_op
                   SK_sort -> SK_type
                   _ -> sk
