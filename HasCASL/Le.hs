{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003-2005
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
import qualified Common.Lib.State as State
import Common.Result
import Common.Id
import Common.AS_Annotation (Named)
import Common.GlobalAnnotations
import Common.Prec

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
data DataEntry = DataEntry IdMap TypeId GenKind [TypeArg] RawKind [AltDefn]
                  deriving (Show, Eq, Ord)

-- | possible definitions for type identifiers
data TypeDefn = NoTypeDefn
              | PreDatatype     -- auxiliary entry for DatatypeDefn
              | DatatypeDefn DataEntry
              | AliasTypeDefn TypeScheme
                deriving (Show, Eq)

-- | for type identifiers also store the raw kind, instances and supertypes
data TypeInfo = TypeInfo { typeKind :: RawKind
                         , otherTypeKinds :: [Kind]
                         , superTypes :: Set.Set TypeId
                         , typeDefn :: TypeDefn
                         } deriving (Show, Eq)

type TypeMap = Map.Map TypeId TypeInfo

-- | the minimal information for a sort
starTypeInfo :: TypeInfo
starTypeInfo = TypeInfo rStar [universe] Set.empty NoTypeDefn

-- | recursively substitute type names within a type
rename :: (TypeId -> RawKind -> Int -> Type) -> Type -> Type
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
data TypeVarDefn = TypeVarDefn Variance VarKind RawKind Int deriving Show

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

-- | the signature is established by the classes, types and assumptions
data Env = Env { classMap :: ClassMap
               , typeMap :: TypeMap
               , localTypeVars :: LocalTypeVars
               , assumps :: Assumps
               , localVars :: Map.Map Id VarDefn
               , sentences :: [Named Sentence]
               , envDiags :: [Diagnosis]
               , preIds :: (PrecMap, Set.Set Id)
               , globAnnos :: GlobalAnnos
               , counter :: Int
               } deriving Show

-- | the empty environment (fresh variables start with 1)
initialEnv :: Env
initialEnv = Env Map.empty Map.empty Map.empty Map.empty Map.empty [] []
             (emptyPrecMap, Set.empty) emptyGlobalAnnos 1

-- * accessing the environment

-- | add diagnostic messages
addDiags :: [Diagnosis] -> State.State Env ()
addDiags ds =
    do e <- State.get
       State.put $ e {envDiags = reverse ds ++ envDiags e}

-- | add sentences
appendSentences :: [Named Sentence] -> State.State Env ()
appendSentences fs =
    do e <- State.get
       State.put $ e {sentences = reverse fs ++ sentences e}

-- | store a class map
putClassMap :: ClassMap -> State.State Env ()
putClassMap ce = do
    e <- State.get
    State.put e { classMap = ce }

-- | store local assumptions
putLocalVars :: Map.Map Id VarDefn -> State.State Env ()
putLocalVars vs =  do
    e <- State.get
    State.put e { localVars = vs }

-- | converting a result to a state computation
fromResult :: (Env -> Result a) -> State.State Env (Maybe a)
fromResult f = do
   e <- State.get
   let Result ds mr = f e
   addDiags ds
   return mr

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

-- | get the variable
getVar :: VarDecl -> Id
getVar(VarDecl v _ _ _) = v

-- | check uniqueness of variables
checkUniqueVars :: [VarDecl] -> State.State Env ()
checkUniqueVars = addDiags . checkUniqueness . map getVar

-- * morphisms

type FunMap = Map.Map (Id, TypeScheme) (Id, TypeScheme)

-- | keep types and class disjoint and use a single identifier map for both
data Morphism = Morphism { msource :: Env
                         , mtarget :: Env
                         , typeIdMap :: IdMap
                         , funMap :: FunMap }
                         deriving Show

-- | construct morphism for subsignatures
mkMorphism :: Env -> Env -> Morphism
mkMorphism e1 e2 = Morphism e1 e2 Map.empty Map.empty

-- * symbol stuff

-- | the type or kind of an identifier
data SymbolType a = OpAsItemType TypeScheme
                  | TypeAsItemType (AnyKind a)
                  | ClassAsItemType (AnyKind a)
                  deriving (Show, Eq, Ord)

-- symbols (may) need the env to look up type aliases
data Symbol = Symbol {symName :: Id, symType :: SymbolType (), symEnv :: Env}
              deriving Show

instance Eq Symbol where
    s1 == s2 = (symName s1, symType s1) == (symName s2, symType s2)

instance Ord Symbol where
    s1 <= s2 = (symName s1, symType s1) <= (symName s2, symType s2)


type SymbolMap = Map.Map Symbol Symbol
type SymbolSet = Set.Set Symbol

idToTypeSymbol :: Env -> Id -> RawKind -> Symbol
idToTypeSymbol e idt k = Symbol idt (TypeAsItemType k) e

idToClassSymbol :: Env -> Id -> RawKind -> Symbol
idToClassSymbol e idt k = Symbol idt (ClassAsItemType k) e

idToOpSymbol :: Env -> Id -> TypeScheme -> Symbol
idToOpSymbol e idt typ = Symbol idt (OpAsItemType typ) e

-- note that the type of a qualified raw symbol is not analysed!
data RawSymbol = AnID Id | AKindedId SymbKind Id
               | AQualId Id (SymbolType ClassId)
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

symbTypeToKind :: SymbolType a -> SymbKind
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
