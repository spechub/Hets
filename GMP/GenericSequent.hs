module GenericSequent where

import AbstractSyntax

-- | Substitution of modal atoms within a "Boole" expression
subst :: Eq a => Boole a -> Clause (Boole a) -> Boole b
subst x s@(Implies neg pos) = 
  case x of
    And phi psi -> And (subst phi s) (subst psi s)
    Not phi     -> Not (subst phi s)
    T           -> T
    F           -> F
    _           -> if (elem x neg) then F
                   else if (elem x pos) then T
                   else error "GenericSequent.subst"

-- | Evaluation of an instantiated "Boole" expression
eval :: Boole a -> Bool
eval x = case x of
           And phi psi -> (eval phi) && (eval psi)
           Not phi     -> not (eval phi)
           T           -> True
           F           -> False
           _           -> error "GenericSequent.eval"


