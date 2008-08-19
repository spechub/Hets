module GMP.GenericSequent where
--   ((-->), (<-->), (\/), (/\), true, false, box, dia, neg, var,  provable)

import Data.List (delete, intersect, nub)

-- | Data type for fomulas
data Form = Var Int -- Var Char (Maybe Int)  -- variables
          | Not !Form             -- ¬A
	        | Box !Form             -- [] A
	        | Conj !Form !Form      -- A/\B
  deriving (Eq)

type Sequent =  [Form]     -- defines a sequent

-- | Show instance for Form datatype
instance Show Form where
  show f = case f of
            Var i    -> "p" ++ show i
            Not g    -> "~" ++ show g
            Box g    -> "[]" ++ show g
            Conj g h -> "(" ++ show g ++ "&" ++ show h ++ ")"

