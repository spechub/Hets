{- |
Module      :  $Header$
Description :  the abstract syntax for analysis and final signature instance
Copyright   :  (c) Christian Maeder and Uni Bremen 2003-2005
License     :  GPLv2 or higher

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

abstract syntax during static analysis
-}

module HasCASL.Le where

import HasCASL.As
import HasCASL.FoldType
import HasCASL.AsUtils
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Common.Lib.State as State
import Common.Result
import Common.Id
import Common.AS_Annotation (Named)
import Common.GlobalAnnotations
import Common.Prec

-- * class info

-- | store the raw kind and all superclasses of a class identifier
data ClassInfo = ClassInfo
    { rawKind :: RawKind
    , classKinds :: Set.Set Kind
    } deriving (Show, Eq, Ord)

-- | mapping class identifiers to their definition
type ClassMap = Map.Map Id ClassInfo

-- * type info

-- | data type generatedness indicator
data GenKind = Free | Generated | Loose deriving (Show, Eq, Ord)

-- | an analysed alternative with a list of (product) types
data AltDefn =
    Construct (Maybe Id) [Type] Partiality [[Selector]]
    -- only argument types
    deriving (Show, Eq, Ord)

-- | an analysed component
data Selector =
    Select (Maybe Id) Type Partiality deriving (Show, Eq, Ord)
    -- only result type

-- | a mapping of type (and disjoint class) identifiers
type IdMap = Map.Map Id Id

{- | data entries are produced from possibly mutual recursive data types. The
top-level identifiers of these types are never renamed but there renaming is
stored in the identifier map. This identifier map must never be empty (even
without renamings) because (the domain of) this map is used to store the
other (recursively dependent) top-level identifiers. -}
data DataEntry =
    DataEntry IdMap Id GenKind [TypeArg] RawKind (Set.Set AltDefn)
    deriving (Show, Eq, Ord)

-- | possible definitions for type identifiers
data TypeDefn =
    NoTypeDefn
  | PreDatatype     -- auxiliary entry for DatatypeDefn
  | DatatypeDefn DataEntry
  | AliasTypeDefn Type
    deriving (Show, Eq)

-- | for type identifiers also store the raw kind, instances and supertypes
data TypeInfo = TypeInfo
    { typeKind :: RawKind
    , otherTypeKinds :: Set.Set Kind
    , superTypes :: Set.Set Id -- only declared or direct supertypes?
    , typeDefn :: TypeDefn
    } deriving Show

instance Eq TypeInfo where
    a == b = compare a b == EQ

instance Ord TypeInfo where
   compare t1 t2 = compare
     (typeKind t1, otherTypeKinds t1, superTypes t1)
     (typeKind t2, otherTypeKinds t2, superTypes t2)

-- | mapping type identifiers to their definition
type TypeMap = Map.Map Id TypeInfo

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
    deriving (Show, Eq, Ord)

instance GetRange Sentence where
  getRange s = case s of
    Formula t -> getRange t
    _ -> nullRange

-- * variables

-- | type variable are kept separately
data TypeVarDefn = TypeVarDefn Variance VarKind RawKind Int deriving Show

-- | mapping type variables to their definition
type LocalTypeVars = Map.Map Id TypeVarDefn

-- | the type of a local variable
data VarDefn = VarDefn Type deriving Show

-- * assumptions

-- | name and scheme of a constructor
data ConstrInfo = ConstrInfo
    { constrId :: Id
    , constrType :: TypeScheme
    } deriving (Show, Eq, Ord)

-- | possible definitions of functions
data OpDefn =
    NoOpDefn OpBrand
  | ConstructData Id     -- ^ target type
  | SelectData (Set.Set ConstrInfo) Id   -- ^ constructors of source type
  | Definition OpBrand Term
    deriving (Show, Eq)

-- | scheme, attributes and definition for function identifiers
data OpInfo = OpInfo
    { opType :: TypeScheme
    , opAttrs :: Set.Set OpAttr
    , opDefn :: OpDefn
    } deriving Show

instance Eq OpInfo where
    o1 == o2 = compare o1 o2 == EQ

instance Ord OpInfo where
    compare o1 o2 = compare (opType o1) $ opType o2

-- | test for constructor
isConstructor :: OpInfo -> Bool
isConstructor o = case opDefn o of
    ConstructData _ -> True
    _ -> False

-- | mapping operation identifiers to their definition
type Assumps = Map.Map Id (Set.Set OpInfo)

-- * the local environment and final signature

-- | the signature is established by the classes, types and assumptions
data Env = Env
    { classMap :: ClassMap
    , typeMap :: TypeMap
    , localTypeVars :: LocalTypeVars
    , assumps :: Assumps
    , binders :: Map.Map Id Id -- binder with associated op-id
    , localVars :: Map.Map Id VarDefn
    , sentences :: [Named Sentence]
    , declSymbs :: Set.Set Symbol
    , envDiags :: [Diagnosis]
    , preIds :: (PrecMap, Set.Set Id)
    , globAnnos :: GlobalAnnos
    , counter :: Int
    } deriving Show

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
                 deriving (Eq, Ord, Show)

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
putLocalVars :: Map.Map Id VarDefn -> State.State Env ()
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
putBinders :: Map.Map Id Id -> State.State Env ()
putBinders bs = do
    e <- State.get
    State.put e { binders = bs }

-- | get the variable
getVar :: VarDecl -> Id
getVar(VarDecl v _ _ _) = v

-- | check uniqueness of variables
checkUniqueVars :: [VarDecl] -> State.State Env ()
checkUniqueVars = addDiags . checkUniqueness . map getVar

-- * morphisms

-- mapping qualified operation identifiers (aka renamings)
type FunMap = Map.Map (Id, TypeScheme) (Id, TypeScheme)

-- | keep types and class disjoint and use a single identifier map for both
data Morphism = Morphism
    { msource :: Env
    , mtarget :: Env
    , typeIdMap :: IdMap
    , classIdMap :: IdMap
    , funMap :: FunMap
    } deriving (Show, Eq, Ord)

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
data SymbolType a =
    OpAsItemType TypeScheme
  | TypeAsItemType (AnyKind a)
  | ClassAsItemType (AnyKind a)
    deriving (Show, Eq, Ord)

-- | symbols with their type and env (to look up type aliases)
data Symbol =
    Symbol {symName :: Id, symType :: SymbolType (), symEnv :: Env}
    deriving Show

instance Eq Symbol where
    s1 == s2 = compare s1 s2 == EQ

instance Ord Symbol where
    compare s1 s2 = compare (symName s1, symType s1) (symName s2, symType s2)

-- | mapping symbols to symbols
type SymbolMap = Map.Map Symbol Symbol

-- | a set of symbols
type SymbolSet = Set.Set Symbol

-- | create a type symbol
idToTypeSymbol :: Env -> Id -> RawKind -> Symbol
idToTypeSymbol e idt k = Symbol idt (TypeAsItemType $ nonVarRawKind k) e

-- | create a class symbol
idToClassSymbol :: Env -> Id -> RawKind -> Symbol
idToClassSymbol e idt k = Symbol idt (ClassAsItemType $ nonVarRawKind k) e

-- | create an operation symbol
idToOpSymbol :: Env -> Id -> TypeScheme -> Symbol
idToOpSymbol e idt typ = Symbol idt (OpAsItemType typ) e

-- | raw symbols where the type of a qualified raw symbol is not yet analysed
data RawSymbol =
    AnID Id
  | AKindedId SymbKind Id
  | AQualId Id (SymbolType Id)
  | ASymbol Symbol
    deriving (Show, Eq, Ord)

-- | mapping raw symbols to raw symbols
type RawSymbolMap = Map.Map RawSymbol RawSymbol

-- | create a raw symbol from an identifier
idToRaw :: Id -> RawSymbol
idToRaw = AnID

-- | extract the top identifer from a raw symbol
rawSymName :: RawSymbol -> Id
rawSymName r = case r of
    AnID i -> i
    AKindedId _ i -> i
    AQualId i _ -> i
    ASymbol s -> symName s

-- | convert a symbol type to a symbol kind
symbTypeToKind :: SymbolType a -> SymbKind
symbTypeToKind s = case s of
    OpAsItemType _ -> SyKop
    TypeAsItemType _ -> SyKtype
    ClassAsItemType _ -> SyKclass

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
    (Map.keysSet $ assumps e) $ Map.keysSet $ typeMap e
    where getCompound (Id _ cs _) = cs
