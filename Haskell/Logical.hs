module Locigal where

not_implemented :: a
not_implemented = error "not implemented"

data Logical = T | F deriving Show

infix 2 \/
infix 3 /\
infix 1 ==>
infix 1 <=> 
infix 1 `oor`
(\/), (/\), (==>), (<=>), oor :: Logical -> Logical -> Logical
neg :: Logical -> Logical
-- unfortunately, already not :: Bool -> Bool
(oor) = not_implemented
(/\) = not_implemented
(\/) = not_implemented
(==>) = not_implemented
(<=>) = not_implemented
neg = not_implemented

-- for any f which is declared but not defined,
-- f = not_implemented should be addded automatically
-- This allows for loose specifications


allof, ex :: (a->Logical) -> Logical
allof = not_implemented
ex = not_implemented

infix 4 ===
(===) :: a->a->Logical
(===) = not_implemented


{-# AXIOMS
         "map_law"       forall f g xs. map f (map g xs) = map (f.g) xs
         "deMorgan"      forall p q. neg p /\ neg q <=> neg (p\/q)
 #-}

-- This is syntactical sugar for 
map_law = allof(\f-> allof(\g -> map (g.f) === map g . map f))
deMorgan = allof(\p -> allof(\q -> neg p /\ neg q <=> neg (p\/q)))


{-

Syntax of AXIOM pragmas:

topdecl : ...
    | '{-# AXIOMS' axioms '#-}'

axiom : STRING formula

formula : quantification formula
        | exp
        | infixexp '=' srcloc exp  -- srcloc just gets source location

quantification : 'forall' rule_var_list '.'   
        | 'exists' rule_var_list '.'
        | 'exists!' rule_var_list '.'


-- from Haskell parser:

rule_var_list 
        : rule_var
        | rule_var rule_var_list

rule_var 
	: varid                              	
       	| '(' varid '::' ctype ')' 


-}