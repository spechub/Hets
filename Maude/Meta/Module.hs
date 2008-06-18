module Maude.Meta.Module where

import Maude.Meta.Qid
import Maude.Meta.Term

import Data.Set (Set)
import Data.Typeable (Typeable)
import qualified Data.Set as Set

{-
*** subsort declarations
  sorts SubsortDecl SubsortDeclSet .
  subsort SubsortDecl < SubsortDeclSet .
-}

data SubsortDecl = Subsort { subsort :: Sort, supersort :: Sort}
    deriving (Show, Eq, Ord, Typeable)

type SubsortDeclSet = Set SubsortDecl


{-
*** sort, kind and type sets
  sorts EmptyTypeSet NeSortSet NeKindSet NeTypeSet SortSet KindSet TypeSet .
  subsort EmptyTypeSet < SortSet KindSet < TypeSet < QidSet .
  subsort Sort < NeSortSet < SortSet .
  subsort Kind < NeKindSet < KindSet .
  subsort Type NeSortSet NeKindSet < NeTypeSet < TypeSet NeQidSet .
-}

type SortSet = Set Sort

type TypeSet = Set Type


{-
*** type lists
  sort NeTypeList TypeList .
  subsorts Type < NeTypeList < TypeList < QidList .
  subsorts NeTypeList < NeQidList .
-}

type TypeList = [Type]


{-
*** sets of type lists
  sort TypeListSet .
  subsort TypeList TypeSet < TypeListSet .
-}

type TypeListSet = Set TypeList


{-
*** attribute sets
  sorts Attr AttrSet .
  subsort Attr < AttrSet .
-}

data Attr =
    -- operator attributes
      Assoc
    | Comm
    | Idem
    | Iter
    | Id Term
    | LeftId Term
    | RightId Term
    | Strat [Int]
    | Memo
    | Prec Int
    | Gather QidList
    | Format QidList
    | Ctor
    | Config
    | Object
    | Msg
    | Frozen [Int]
    | Poly [Int]
    | Special HookList
    -- statement attributes
    | Label Qid
    | Metadata String
    | Owise
    | Nonexec
    deriving (Show, Eq, Ord, Typeable)

type AttrSet = Set Attr


{-
*** renamings
  sorts Renaming RenamingSet .
  subsort Renaming < RenamingSet .
-}

data Renaming = Sort'To { from :: Qid, to :: Qid }
              | Op'To { from :: Qid, to :: Qid, attrs :: AttrSet }
              | Op'Type'To { from :: Qid, range :: TypeList, domain :: Type, to :: Qid, attrs :: AttrSet }
              | Label'To { from :: Qid, to :: Qid }
    deriving (Show, Eq, Ord, Typeable)

type RenamingSet = Set Renaming


{-
*** parameter lists
  sort EmptyCommaList NeParameterList ParameterList .
  subsorts Sort < NeParameterList < ParameterList .
  subsort EmptyCommaList < GroundTermList ParameterList .
-}

type ParameterList = [Sort]


{-
*** module expressions
  sort ModuleExpression .
  subsort Qid < ModuleExpression .
-}

data ModuleExpression = ModName { mod'name :: Qid }
                      | ModJoin { mod'left :: ModuleExpression, mod'right :: ModuleExpression }
                      | ModRename { mod'module :: ModuleExpression, mod'rename :: RenamingSet }
                      | ModInstantiate { mod'module :: ModuleExpression, mod'params :: ParameterList }
    deriving (Show, Eq, Ord, Typeable)


{-
*** parameter declarations
  sorts ParameterDecl NeParameterDeclList ParameterDeclList .
  subsorts ParameterDecl < NeParameterDeclList < ParameterDeclList .
-}

data ParameterDecl = Parameter Sort ModuleExpression    -- I can't think of sensible names for these.
    deriving (Show, Eq, Ord, Typeable)

type ParameterDeclList = [ParameterDecl]


{-
*** importations
  sorts Import ImportList .
  subsort Import < ImportList .
-}

data Import = Protecting { imp'module :: ModuleExpression }
            | Extending  { imp'module :: ModuleExpression }
            | Including  { imp'module :: ModuleExpression }
    deriving (Show, Eq, Ord, Typeable)

type ImportList = [Import]


{-
*** hooks
  sorts Hook NeHookList HookList .
  subsort Hook < NeHookList < HookList .
-}

data Hook = IdHook Qid QidList
          | OpHook Qid Qid QidList Qid
          | TermHook Qid Term
    deriving (Show, Eq, Ord, Typeable)

type HookList = [Hook]


{-
sorts OpDecl OpDeclSet .
subsort OpDecl < OpDeclSet .
-}

data OpDecl = Op { op'name :: Qid, op'range :: TypeList, op'domain :: Type, op'attrs :: AttrSet }
    deriving (Show, Eq, Ord, Typeable)

type OpDeclSet = Set OpDecl


{-
*** conditions
  sorts EqCondition Condition .
  subsort EqCondition < Condition .
-}

data Condition = Nil
               | Equal Term Term
               | Member Term Sort
               | Match Term Term
               | Implies Term Term
               | Conjunction Condition Condition
    deriving (Show, Eq, Ord, Typeable)

{- TODO:
* Equations and Memberships can only use EqCondition; also, "Implies" is completely wrong.
-}


{-
*** membership axioms
  sorts MembAx MembAxSet .
  subsort MembAx < MembAxSet .
-}

data MembAx = Mb Term Sort AttrSet
            | Cmb Term Sort Condition AttrSet   -- EqCondition, actually!
    deriving (Show, Eq, Ord, Typeable)

type MembAxSet = Set MembAx


{-
*** equations
  sorts Equation EquationSet .
  subsort Equation < EquationSet .
-}

data Equation = Eq Term Term AttrSet
              | Ceq Term Term Condition AttrSet -- EqCondition, actually!
    deriving (Show, Eq, Ord, Typeable)

type EquationSet = Set Equation


{-
*** rules
  sorts Rule RuleSet .
  subsort Rule < RuleSet .
-}

data Rule = Rl Term Term AttrSet
          | Crl Term Term Condition AttrSet
    deriving (Show, Eq, Ord, Typeable)

type RuleSet = Set Rule


{-
*** modules
  sorts FModule SModule FTheory STheory Module .
  subsorts FModule < SModule < Module .
  subsorts FTheory < STheory < Module .
  sort Header .
  subsort Qid < Header .
-}

data Header = Name { h'name :: Qid }
            | Head { h'name :: Qid, h'params :: ParameterDeclList }
    deriving (Show, Eq, Ord, Typeable)

class Module a where
    modName :: a -> Qid
    modImports :: a -> ImportList
    modSorts :: a -> SortSet
    modSubsorts :: a -> SubsortDeclSet
    modOps :: a -> OpDeclSet
    modMbs :: a -> MembAxSet
    modEqs :: a -> EquationSet
    modRls :: a -> RuleSet

data FModule = FMod {
        fm'name :: Header,
        fm'imports :: ImportList,
        fm'sorts :: SortSet,
        fm'subsorts :: SubsortDeclSet,
        fm'ops :: OpDeclSet,
        fm'mbs :: MembAxSet,
        fm'eqs :: EquationSet
    } deriving (Show, Eq, Ord, Typeable)

instance Module FModule where
    modName     = h'name . fm'name
    modImports  = fm'imports
    modSorts    = fm'sorts
    modSubsorts = fm'subsorts
    modOps      = fm'ops
    modMbs      = fm'mbs
    modEqs      = fm'eqs
    modRls _    = Set.empty

data SModule = Mod {
        m'name :: Header,
        m'imports :: ImportList,
        m'sorts :: SortSet,
        m'subsorts :: SubsortDeclSet,
        m'ops :: OpDeclSet,
        m'mbs :: MembAxSet,
        m'eqs :: EquationSet,
        m'rls :: RuleSet
    } deriving (Show, Eq, Ord, Typeable)

instance Module SModule where
    modName     = h'name . m'name
    modImports  = m'imports
    modSorts    = m'sorts
    modSubsorts = m'subsorts
    modOps      = m'ops
    modMbs      = m'mbs
    modEqs      = m'eqs
    modRls      = m'rls

data FTheory = FTh {
        fth'name :: Qid,
        fth'imports :: ImportList,
        fth'sorts :: SortSet,
        fth'subsorts :: SubsortDeclSet,
        fth'ops :: OpDeclSet,
        fth'mbs :: MembAxSet,
        fth'eqs :: EquationSet
    } deriving (Show, Eq, Ord, Typeable)

instance Module FTheory where
    modName     = fth'name
    modImports  = fth'imports
    modSorts    = fth'sorts
    modSubsorts = fth'subsorts
    modOps      = fth'ops
    modMbs      = fth'mbs
    modEqs      = fth'eqs
    modRls _    = Set.empty

data STheory = Th {
        th'name :: Qid,
        th'imports :: ImportList,
        th'sorts :: SortSet,
        th'subsorts :: SubsortDeclSet,
        th'ops :: OpDeclSet,
        th'mbs :: MembAxSet,
        th'eqs :: EquationSet,
        th'rls :: RuleSet
    } deriving (Show, Eq, Ord, Typeable)

instance Module STheory where
    modName     = th'name
    modImports  = th'imports
    modSorts    = th'sorts
    modSubsorts = th'subsorts
    modOps      = th'ops
    modMbs      = th'mbs
    modEqs      = th'eqs
    modRls      = th'rls

{- NOTE:
Modules are "supersets" of signatures, so I should be able to declare
  instance (Module a) => Signature a where ...
Morphisms are more closely related to renamings, so I should use those.
Also, Views aren't currently represented at the meta level.

Outstanding Issues:
* Haskell doesn't support subtyping as easily as Maude does.
* Theories in Maude cannot be parameterized (Views can in Full Maude).
* I'm still missing lots of "scaffolding" types.
* This Haskell mode ... needs improvement, should switch back to Emacs.
-}
