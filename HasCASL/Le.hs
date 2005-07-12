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
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.Result(Diagnosis)
import Common.Id
import Common.AS_Annotation(Named)

-- * class info

-- | store the raw kind and all superclasses of a class identifier 
data ClassInfo = ClassInfo { rawKind :: RawKind
                           , classKinds :: [Kind]
                           } deriving (Show, Eq)

type ClassMap = Map.Map ClassId ClassInfo

-- * type info

-- | data type generatedness indicator 
data GenKind = Free | Generated | Loose deriving (Show, Eq, Ord) 

-- | an analysed alternative with a list of (product) types 
data AltDefn = Construct (Maybe UninstOpId) [Type] Partiality [[Selector]] 
               -- only argument types
               deriving (Show, Eq, Ord) 

-- | an analysed component
data Selector = Select (Maybe UninstOpId) Type Partiality -- only result type
                deriving (Show, Eq, Ord) 

-- | a mapping of type (and disjoint class) identifiers 
type IdMap = Map.Map TypeId TypeId

-- | for data types the morphism needs to be kept as well
data DataEntry = DataEntry IdMap TypeId GenKind [TypeArg] [AltDefn]
                  deriving (Show, Eq, Ord)

-- | possible definitions for type identifiers
data TypeDefn = NoTypeDefn
              | PreDatatype     -- auxiliary entry for DatatypeDefn
              | Supertype Vars TypeScheme Term 
              | DatatypeDefn DataEntry
              | AliasTypeDefn TypeScheme
                deriving (Show, Eq)

-- | for type identifiers also store the raw kind, instances and supertypes
data TypeInfo = TypeInfo { typeKind :: RawKind
                         , otherTypeKinds :: [Kind]
                         , superTypes :: [Type]
                         , typeDefn :: TypeDefn
                         } deriving (Show, Eq)

type TypeMap = Map.Map TypeId TypeInfo

-- | the minimal information for a sort
starTypeInfo :: TypeInfo
starTypeInfo = TypeInfo star [star] [] NoTypeDefn

-- | recursively substitute type names within a type 
rename :: (TypeId -> Kind -> Int -> Type) -> Type -> Type
rename m t = case t of
           TypeName i k n -> m i k n
           TypeAppl t1 t2 -> TypeAppl (rename m t1) (rename m t2)
           ExpandedType t1 t2 -> ExpandedType (rename m t1) (rename m t2)
           TypeToken _ -> t
           BracketType b l ps ->
               BracketType b (map (rename m) l) ps
           KindedType tk k ps -> 
               KindedType (rename m tk) k ps
           MixfixType l -> MixfixType $ map (rename m) l
           LazyType tl ps -> LazyType (rename m tl) ps
           ProductType l ps -> ProductType (map (rename m) l) ps
           FunType t1 a t2 ps -> FunType (rename m t1) a (rename m t2) ps

-- | rename the type according to identifier map (for comorphisms)
mapType :: IdMap -> Type -> Type
mapType m ty = if Map.null m then ty else 
              rename ( \ i k n ->
               let t = TypeName i k n in
               if n == 0 then 
                  case Map.lookup i m of
                  Just j -> TypeName j k 0
                  _ -> t
               else t) ty

-- * sentences

-- | data types are also special sentences because of their properties 
data Sentence = Formula Term
              | DatatypeSen [DataEntry]
              | ProgEqSen UninstOpId TypeScheme ProgEq
                deriving (Show, Eq, Ord)
 
-- * variables

-- | type variable are kept separately
data TypeVarDefn = TypeVarDefn RawKind VarKind Int deriving Show

type LocalTypeVars = Map.Map TypeId TypeVarDefn

-- | the type of a local variable
data VarDefn = VarDefn Type deriving Show

-- * assumptions

-- | name and scheme of a constructor
data ConstrInfo = ConstrInfo { constrId :: UninstOpId
                             , constrType :: TypeScheme 
                             } deriving (Show, Eq)

-- | possible definitions of functions 
data OpDefn = NoOpDefn OpBrand
            | ConstructData TypeId     -- target type
            | SelectData [ConstrInfo] TypeId   -- constructors of source type
            | Definition OpBrand Term
              deriving (Show, Eq)

-- | scheme, attributes and definition for function identifiers
data OpInfo = OpInfo { opType :: TypeScheme
                     , opAttrs :: [OpAttr]
                     , opDefn :: OpDefn
                     } deriving (Show, Eq)

-- | test for constructor
isConstructor :: OpInfo -> Bool
isConstructor o = case opDefn o of
                    ConstructData _ -> True
                    _ -> False

-- | a list of infos for overloaded functions
data OpInfos = OpInfos { opInfos :: [OpInfo] } deriving (Show, Eq)

type Assumps = Map.Map UninstOpId OpInfos

-- * the local environment and final signature 

-- | the precedence map
type PrecMap = (Map.Map Id Int, Int, Int)

-- | the signature is established by the classes, types and assumptions
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

-- | the empty environment (fresh variables start with 1)
initialEnv :: Env
initialEnv = Env Map.empty Map.empty Map.empty Map.empty Map.empty [] [] 
             ((Map.empty, 0, 0), Set.empty) 1

-- * symbol stuff

-- | the type or kind of an identifier
data SymbolType = OpAsItemType TypeScheme
                | TypeAsItemType Kind
                | ClassAsItemType Kind
                  deriving (Show, Eq, Ord)

-- symbols (may) need the env to look up type aliases
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
