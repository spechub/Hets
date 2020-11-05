{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}
{- |
Module      :  ./HasCASL/Le.hs
Description :  the abstract syntax for analysis and final signature instance
Copyright   :  (c) Christian Maeder and Uni Bremen 2003-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

abstract syntax during static analysis
-}

module HasCASL.Le where

import HasCASL.As
import HasCASL.FoldType
import HasCASL.AsUtils

import qualified Common.Lib.State as State
import Common.Result
import Common.Id
import Common.AS_Annotation (Named)
import Common.GlobalAnnotations
import Common.Prec

import Data.Data
import Data.Ord
import qualified Data.HashMap.Lazy as Map
import qualified Data.Set as Set

import GHC.Generics (Generic)
import Data.Hashable

-- * class info

-- | store the raw kind and all superclasses of a class identifier
data ClassInfo = ClassInfo
    { rawKind :: RawKind
    , classKinds :: Set.Set Kind
    } deriving (Show, Eq, Ord, Typeable, Data)

-- | mapping class identifiers to their definition
type ClassMap = Map.HashMap Id ClassInfo

-- * type info

-- | data type generatedness indicator
data GenKind = Free | Generated | Loose deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable GenKind

-- | an analysed alternative with a list of (product) types
data AltDefn =
    Construct (Maybe Id) [Type] Partiality [[Selector]]
    -- only argument types
    deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable AltDefn

-- | an analysed component
data Selector =
    Select (Maybe Id) Type Partiality deriving (Show, Eq, Ord, Typeable, Data, Generic)
    -- only result type

instance Hashable Selector

-- | a mapping of type (and disjoint class) identifiers
type IdMap = Map.HashMap Id Id

{- | data entries are produced from possibly mutual recursive data types. The
top-level identifiers of these types are never renamed but there renaming is
stored in the identifier map. This identifier map must never be empty (even
without renamings) because (the domain of) this map is used to store the
other (recursively dependent) top-level identifiers. -}
data DataEntry =
    DataEntry IdMap Id GenKind [TypeArg] RawKind (Set.Set AltDefn)
    deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable DataEntry

-- | possible definitions for type identifiers
data TypeDefn =
    NoTypeDefn
  | PreDatatype     -- auxiliary entry for DatatypeDefn
  | DatatypeDefn DataEntry
  | AliasTypeDefn Type
    deriving (Show, Eq, Ord, Typeable, Data)

-- | for type identifiers also store the raw kind, instances and supertypes
data TypeInfo = TypeInfo
    { typeKind :: RawKind
    , otherTypeKinds :: Set.Set Kind
    , superTypes :: Set.Set Id -- only declared or direct supertypes?
    , typeDefn :: TypeDefn
    } deriving (Show, Typeable, Data)

instance Eq TypeInfo where
    a == b = compare a b == EQ

instance Ord TypeInfo where
   compare t1 t2 = compare
     (typeKind t1, otherTypeKinds t1, superTypes t1)
     (typeKind t2, otherTypeKinds t2, superTypes t2)

-- | mapping type identifiers to their definition
type TypeMap = Map.HashMap Id TypeInfo

-- | the minimal information for a sort
starTypeInfo :: TypeInfo
starTypeInfo = TypeInfo rStar (Set.singleton universe) Set.empty NoTypeDefn

-- | rename the type according to identifier map (for comorphisms)
mapType :: IdMap -> Type -> Type
mapType m = if Map.null m then id else
    foldType mapTypeRec
    { foldTypeName = \ t i k n -> if n /= 0 then t else
        case Map.lookup i m of
          Just j -> TypeName j k 0
          Nothing -> t }

-- * sentences

-- | data types are also special sentences because of their properties
data Sentence =
    Formula Term
  | DatatypeSen [DataEntry]
  | ProgEqSen Id TypeScheme ProgEq
    deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable Sentence

instance GetRange Sentence where
  getRange s = case s of
    Formula t -> getRange t
    _ -> nullRange

-- * variables

-- | type variable are kept separately
data TypeVarDefn = TypeVarDefn Variance VarKind RawKind Int
  deriving (Show, Typeable, Data)

-- | mapping type variables to their definition
type LocalTypeVars = Map.HashMap Id TypeVarDefn

-- | the type of a local variable
data VarDefn = VarDefn Type deriving (Show, Typeable, Data)

-- * assumptions

-- | name and scheme of a constructor
data ConstrInfo = ConstrInfo
    { constrId :: Id
    , constrType :: TypeScheme
    } deriving (Show, Eq, Ord, Typeable, Data)

-- | possible definitions of functions
data OpDefn =
    NoOpDefn OpBrand
  | ConstructData Id     -- ^ target type
  | SelectData (Set.Set ConstrInfo) Id   -- ^ constructors of source type
  | Definition OpBrand Term
    deriving (Show, Eq, Ord, Typeable, Data)

-- | scheme, attributes and definition for function identifiers
data OpInfo = OpInfo
    { opType :: TypeScheme
    , opAttrs :: Set.Set OpAttr
    , opDefn :: OpDefn
    } deriving (Show, Typeable, Data)

instance Eq OpInfo where
    o1 == o2 = compare o1 o2 == EQ

instance Ord OpInfo where
    compare = comparing opType

-- | test for constructor
isConstructor :: OpInfo -> Bool
isConstructor o = case opDefn o of
    ConstructData _ -> True
    _ -> False

-- | mapping operation identifiers to their definition
type Assumps = Map.HashMap Id (Set.Set OpInfo)

-- * the local environment and final signature

-- | the signature is established by the classes, types and assumptions
data Env = Env
    { classMap :: ClassMap
    , typeMap :: TypeMap
    , localTypeVars :: LocalTypeVars
    , assumps :: Assumps
    , binders :: Map.HashMap Id Id -- binder with associated op-id
    , localVars :: Map.HashMap Id VarDefn
    , sentences :: [Named Sentence]
    , declSymbs :: Set.Set Symbol
    , envDiags :: [Diagnosis]
    , preIds :: (PrecMap, Set.Set Id)
    , globAnnos :: GlobalAnnos
    , counter :: Int
    } deriving (Show, Typeable, Data)

instance Eq Env where
    a == b = compare a b == EQ

instance Ord Env where
  compare e1 e2 = compare
    (classMap e1, typeMap e1, assumps e1)
    (classMap e2, typeMap e2, assumps e2)

-- | the empty environment (fresh variables start with 1)
initialEnv :: Env
initialEnv = Env
    { classMap = Map.empty
    , typeMap = Map.empty
    , localTypeVars = Map.empty
    , assumps = Map.empty
    , binders = Map.empty
    , localVars = Map.empty
    , sentences = []
    , declSymbs = Set.empty
    , envDiags = []
    , preIds = (emptyPrecMap, Set.empty)
    , globAnnos = emptyGlobalAnnos
    , counter = 1 }

{- utils for singleton sets that could also be part of "Data.Set". These
functions rely on 'Data.Set.size' being computable in constant time and
would need to be rewritten for set implementations with a size
function that is only linear. -}

data Constrain = Kinding Type Kind
               | Subtyping Type Type
                 deriving (Show, Eq, Ord, Typeable, Data)

-- * accessing the environment

-- | add diagnostic messages
addDiags :: [Diagnosis] -> State.State Env ()
addDiags ds = do
    e <- State.get
    State.put $ e {envDiags = reverse ds ++ envDiags e}

-- | add sentences
appendSentences :: [Named Sentence] -> State.State Env ()
appendSentences fs = do
    e <- State.get
    State.put $ e {sentences = reverse fs ++ sentences e}

-- | store a class map
putClassMap :: ClassMap -> State.State Env ()
putClassMap ce = do
    e <- State.get
    State.put e { classMap = ce }

-- | store local assumptions
putLocalVars :: Map.HashMap Id VarDefn -> State.State Env ()
putLocalVars vs = do
    e <- State.get
    State.put e { localVars = vs }

-- | converting a result to a state computation
fromResult :: (Env -> Result a) -> State.State Env (Maybe a)
fromResult f = do
   e <- State.get
   let Result ds mr = f e
   addDiags ds
   return mr

-- | add the symbol to the state
addSymbol :: Symbol -> State.State Env ()
addSymbol sy = do
    e <- State.get
    State.put e { declSymbs = Set.insert sy $ declSymbs e }

-- | store local type variables
putLocalTypeVars :: LocalTypeVars -> State.State Env ()
putLocalTypeVars tvs = do
    e <- State.get
    State.put e { localTypeVars = tvs }

-- | store a complete type map
putTypeMap :: TypeMap -> State.State Env ()
putTypeMap tm = do
    e <- State.get
    State.put e { typeMap = tm }

-- | store assumptions
putAssumps :: Assumps -> State.State Env ()
putAssumps ops = do
    e <- State.get
    State.put e { assumps = ops }

-- | store assumptions
putBinders :: Map.HashMap Id Id -> State.State Env ()
putBinders bs = do
    e <- State.get
    State.put e { binders = bs }

-- | get the variable
getVar :: VarDecl -> Id
getVar (VarDecl v _ _ _) = v

-- | check uniqueness of variables
checkUniqueVars :: [VarDecl] -> State.State Env ()
checkUniqueVars = addDiags . checkUniqueness . map getVar

-- * morphisms

-- mapping qualified operation identifiers (aka renamings)
type FunMap = Map.HashMap (Id, TypeScheme) (Id, TypeScheme)

-- | keep types and class disjoint and use a single identifier map for both
data Morphism = Morphism
    { msource :: Env
    , mtarget :: Env
    , typeIdMap :: IdMap
    , classIdMap :: IdMap
    , funMap :: FunMap
    } deriving (Show, Eq, Ord, Typeable, Data)

-- | construct morphism for subsignatures
mkMorphism :: Env -> Env -> Morphism
mkMorphism e1 e2 = Morphism
    { msource = e1
    , mtarget = e2
    , typeIdMap = Map.empty
    , classIdMap = Map.empty
    , funMap = Map.empty }

isInclMor :: Morphism -> Bool
isInclMor m =
   Map.null (typeIdMap m) && Map.null (classIdMap m) && Map.null (funMap m)

-- * symbol stuff

-- | the type or kind of an identifier
data SymbolType =
    OpAsItemType TypeScheme
  | TypeAsItemType RawKind
  | ClassAsItemType RawKind
  | SuperClassSymbol Kind
  | TypeKindInstance Kind
  | SuperTypeSymbol Id
  | TypeAliasSymbol Type
  | PredAsItemType TypeScheme
    deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable SymbolType

-- | symbols with their type
data Symbol =
    Symbol { symName :: Id, symType :: SymbolType }
    deriving (Show, Typeable, Data, Generic)

instance Hashable Symbol

instance Eq Symbol where
    s1 == s2 = compare s1 s2 == EQ

instance Ord Symbol where
    compare s1 s2 = compare (symName s1, symType s1) (symName s2, symType s2)

-- | mapping symbols to symbols
type SymbolMap = Map.HashMap Symbol Symbol

-- | a set of symbols
type SymbolSet = Set.Set Symbol

-- | create a type symbol
idToTypeSymbol :: Id -> RawKind -> Symbol
idToTypeSymbol idt k = Symbol idt (TypeAsItemType $ nonVarRawKind k)

-- | create a class symbol
idToClassSymbol :: Id -> RawKind -> Symbol
idToClassSymbol idt k = Symbol idt (ClassAsItemType $ nonVarRawKind k)

-- | create an operation symbol
idToOpSymbol :: Id -> TypeScheme -> Symbol
idToOpSymbol idt typ = Symbol idt (OpAsItemType typ)

{- | raw symbols where the type of a qualified raw symbol can be a type scheme
and also be a kind if the symbol kind is unknown. -}
data RawSymbol =
    AnID Id
  | AKindedId SymbKind Id
  | ASymbol Symbol
    deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable RawSymbol

-- | mapping raw symbols to raw symbols
type RawSymbolMap = Map.HashMap RawSymbol RawSymbol

-- | create a raw symbol from an identifier
idToRaw :: Id -> RawSymbol
idToRaw = AnID

-- | extract the top identifer from a raw symbol
rawSymName :: RawSymbol -> Id
rawSymName r = case r of
    AnID i -> i
    AKindedId _ i -> i
    ASymbol s -> symName s

-- | convert a symbol type to a symbol kind
symbTypeToKind :: SymbolType -> SymbKind
symbTypeToKind s = case s of
    OpAsItemType _ -> SyKop
    TypeAsItemType _ -> SyKtype
    SuperTypeSymbol _ -> SyKtype
    TypeKindInstance _ -> SyKtype
    TypeAliasSymbol _ -> SyKtype
    ClassAsItemType _ -> SyKclass
    SuperClassSymbol _ -> SyKclass
    PredAsItemType _ -> SyKpred

-- | wrap a symbol as raw symbol (is 'ASymbol')
symbolToRaw :: Symbol -> RawSymbol
symbolToRaw = ASymbol

-- | create a raw symbol from a symbol kind and an identifier
symbKindToRaw :: SymbKind -> Id -> RawSymbol
symbKindToRaw sk = case sk of
    Implicit -> AnID
    _ -> AKindedId $ case sk of
        SyKpred -> SyKop
        SyKfun -> SyKop
        SyKsort -> SyKtype
        _ -> sk

getCompoundLists :: Env -> Set.Set [Id]
getCompoundLists e = Set.delete [] $ Set.map getCompound $ Set.union
    (Set.fromList $ Map.keys $ assumps e) $ Set.fromList $ Map.keys $ typeMap e
    where getCompound (Id _ cs _) = cs
