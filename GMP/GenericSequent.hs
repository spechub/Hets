{-# OPTIONS -XMultiParamTypeClasses -XFlexibleInstances #-}
module GMP.GenericSequent where
-- ((-->), (<-->), (\/), (/\), true, false, box, dia, neg, var,  provable)

-- import Data.List (delete, intersect, nub)

-- | Datatype for fomulas
data Form a b = Var Char (Maybe Int)              -- variables
              | Not !(Form a b)                   -- negation: ¬
	            | M a !(Form b a)                   -- modal atom: [] A
	            | Conj !(Form a b) !(Form a b)      -- conjunction: A/\B
  deriving (Eq, Show)

-- | Datatype for defining a sequent
type Sequent a b = [Form a b]

{- | Logic Class : two "ordered" modal logic types with "clause" matching rule
 -}
class (Eq a, Eq b, Show a, Show b) => Logic a b where
  match :: Sequent a b -> [Sequent b a]

-- | Datatypes for the supported logics
data K = K deriving (Eq, Show)
data KD = KD deriving (Eq, Show)

-- | Instance of logic K & a
instance (Show a, Eq a) => Logic K a where
  match x = []

-- ............



------------------------------------------------------------------------------

-- | "False" as deduced out of the Form datatype
false :: Form a b
false = Conj (Var ' ' Nothing) (Not (Var ' ' Nothing))

-- | "Negation" of a form
neg :: Form a b -> Form a b
neg x = Not x

-- | "True" as deduced from "False" and "Negation"
true :: Form a b
true = neg false

