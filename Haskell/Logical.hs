module Haskell.Logical where

not_implemented :: a
not_implemented = error "not implemented"

data Logical = T | F deriving Show

infix 2 \/
infix 3 /\
infix 1 ==>
infix 1 <=> 
(\/), (/\), (==>), (<=>) :: Logical -> Logical -> Logical
not :: Logical -> Logical

-- unfortunately, already not :: Bool -> Bool
(/\) = not_implemented
(\/) = not_implemented
(==>) = not_implemented
(<=>) = not_implemented
not = not_implemented

infix 4 ===
(===) :: a->a->Logical
(===) = not_implemented

-- for any f which is declared but not defined,
-- f = not_implemented should be addded automatically
-- This allows for loose specifications

allof, ex, exone :: (a->Logical) -> Logical
allof = not_implemented
ex = not_implemented
exone = not_implemented

