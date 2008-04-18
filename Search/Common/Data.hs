module Search.Common.Data where

import Data.Map

data Formula c v = Const c [Formula c v] | Var v [Formula c v] 
                 | Binder c [v] (Formula c v) deriving (Eq,Ord)
data Constant c = TrueAtom | FalseAtom | Not | And | Or | Imp | Eqv | Xor | Equal
                | All | Some | LogicDependent c deriving (Eq,Ord)

type Skeleton c = Formula (Constant c) Int


type Skel = String -- ???
type LibraryName = String
type TheoryName = String
type ParamString = String -- ???
type LineNr = Int
type Renaming a = Map a a
type LineMap = Map Int Int
type ProfileMorphism a = (Renaming a, LineMap)

data Role = Axiom | Theorem deriving (Eq, Ord, Show)
type SenType = String

type ShortProfile p = (Skel, [p], LineNr, SenType)
type LongInclusionTuple p = (TheoryName, TheoryName, Renaming p, LineMap, [LineNr])

type Strength = String

data Profile f s p =
    Profile 
    { libName ::LibraryName,
      theoryName :: TheoryName,
      lineNr :: Int,
      formula :: f,
      skeleton :: s,
      parameter :: [p],
      role :: Role,
      strength :: Strength
    } deriving (Eq, Ord, Show)

