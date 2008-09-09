module Search.Common.Data where

import Data.Map
import Search.Utils.List (mapShow)

data Formula c v = Const c [Formula c v] | Var v [Formula c v] 
                 | Binder c [v] (Formula c v) deriving (Eq,Ord)
data Constant c = TrueAtom | FalseAtom | Not | And | Or | Imp | Eqv | Xor | Equal
                | All | Some | LogicDependent c deriving (Eq,Ord)

type Skeleton c = Formula (Constant c) Int


instance (Show c,Show v) => Show (Formula c v) where
    show (Const c []) = show c
    show (Const c args) = "(" ++ show c ++ " " ++ (mapShow " " args) ++ ")"
    show (Var c []) = show c
    show (Var v args) = "(" ++ show v ++ " " ++  (mapShow " " args) ++ ")"
    show (Binder c vars body) = "(" ++ show c ++ " (" ++ (mapShow " " vars) ++ ") " ++ show body ++ ")"

instance (Show c) => Show (Constant c)
    where show TrueAtom = "true"
          show FalseAtom = "false"
          show Not = "not"
          show And = "and"
          show Or = "or"
          show Imp = "imp"
	  show Eqv = "eqv"
          show Xor = "xor"
	  show Equal = "eq"
          show All = "all"
          show Some = "some"
          show (LogicDependent c) = "_" ++ show c

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

