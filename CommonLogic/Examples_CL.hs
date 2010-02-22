module Examples_CL where

import AS_CommonLogic

-- Examples

n1 :: NAME
n1 = "foo"

t1 :: TERM
t1 = Name n1
t2 :: TERM
t2 = Funct_term (Name "foo") (Term_seq [t1])

a1 :: ATOM
a1 = Equation t1 t1
a2 :: ATOM
a2 = Atom (Name n1) (Term_seq [t1, t1])

s1 :: SENTENCE
s1 = Atom_sent a1

b1 :: BOOL_SENT
b1 = Conjunction [s1]
b2 :: BOOL_SENT
b2 = Implication s1 s2

s2 :: SENTENCE
s2 = Bool_sent b1

i1 :: IMPORTATION
i1 = Imp_name "Import"

text1 :: TEXT
text1 = Text [Sentence s1, Sentence s2]

-- Cat(a) :: atom
cat :: ATOM
cat = Atom (Name "Cat") (Term_seq [Name "a"])

-- Cat(a) or Cat(a)
b3 :: BOOL_SENT
b3 = Disjunction [Atom_sent cat, Atom_sent cat]
s3 :: SENTENCE
s3 = Bool_sent b3
