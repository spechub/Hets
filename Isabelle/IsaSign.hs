{- |
Module      :  $Header$
Copyright   :  (c) University of Cambridge, Cambridge, England
               adaption (c) Till Mossakowski, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   Data structures for Isabelle signatures and theories.
   Adapted from Isabelle.
-}

module Isabelle.IsaSign where

import qualified Common.Lib.Map as Map

-- temporary!!
type Axiom = ()

-------------------- not quite from src/Pure/term.ML ------------------------

{-Indexnames can be quickly renamed by adding an offset to the integer part,
  for resolution.-}
type Indexname = (String,Int)

{- Types are classified by sorts. -}

-- Classes

data IsaClass  = IsaClass { classId :: String, classDef :: [Axiom] }
                 deriving (Ord, Eq, Show)   

type Sort  = [IsaClass]

domain:: Sort
domain = [pcpo]

isaTerm :: IsaClass
isaTerm = IsaClass "term" []

holType :: Sort
holType = [IsaClass "hol_type" []]

pcpo :: IsaClass
pcpo = IsaClass "pcpo" []

ho_ho :: [Sort]
ho_ho = [holType, holType]


------------------------------------------------------------------------------

{- The sorts attached to TFrees and TVars specify the sort of that variable -}
data Typ = Type  { typeId         :: String,
                   typeArgKind    :: [Sort],
                   typeResultKind :: Sort,
                   typeArgs  :: [Typ] } 
         | TFree { typeId    :: String,
                   typeSort  :: Sort}
         | TVar  { indexname :: Indexname, -- (String,Int)
                   typeSort  :: Sort }
         deriving (Eq, Ord, Show)

noType :: Typ
noType = dummyT

dummyT :: Typ
dummyT = Type "dummy" [] holType []

boolType :: Typ
boolType = Type "bool" [] holType []

mkOptionType :: Typ -> Typ
mkOptionType t = Type "option" [holType] holType [t]

prodS :: String 
prodS = "*"    -- this is printed as it is!

prodType :: Typ -> Typ -> Typ
prodType t1 t2 = Type prodS ho_ho holType [t1,t2]

typeApplS :: String 
typeApplS = "typeAppl" -- maybe this should be " " for printing

mkTypeAppl :: Typ -> Typ -> Typ
mkTypeAppl t1 t2 = Type typeApplS ho_ho holType [t1,t2]

funS :: String 
funS = "fun"  -- may be this should be "=>" for printing

mkFunType :: Typ -> Typ -> Typ
mkFunType s t = Type funS ho_ho holType [s,t] -- was "-->" before

{-handy for multiple args: [T1,...,Tn]--->T  gives  T1-->(T2--> ... -->T)-}
mkCurryFunType :: [Typ] -> Typ -> Typ
mkCurryFunType = flip $ foldr mkFunType -- was "--->" before

voidDom :: Typ
voidDom = Type "void" [] domain []
-- voidDom = Type ("void",[pcpo],[])

{- should this be included (as primitive)? -}
flatDom :: Typ
flatDom = Type "flat" [] domain []

{- sort is ok? -}
mkContFun :: Typ -> Typ -> Typ
mkContFun t1 t2 = Type "dFun" [domain, domain] domain [t1,t2]

mkDomProduct :: Typ -> Typ -> Typ
mkDomProduct t1 t2 = Type "**" [domain, domain] domain [t1,t2]

mkDomSum :: Typ -> Typ -> Typ
mkDomSum t1 t2 = Type "++" [domain, domain] domain [t1,t2]

mkDomAppl :: Typ -> Typ -> Typ 
mkDomAppl t1 t2 = Type "domAppl" [domain, domain] domain [t1,t2]

{-Terms.  Bound variables are indicated by depth number.
  Free variables, (scheme) variables and constants have names.
  A term is "closed" if every bound variable of level "lev"
  is enclosed by at least "lev" abstractions.

  It is possible to create meaningless terms containing loose bound vars
  or type mismatches.  But such terms are not allowed in rules. -}

data Flag = IsCont | NotCont deriving (Eq, Ord ,Show)

data Term =
        Const { termBasicId  :: String, 
                termType     :: Typ, 
                defaultClass :: IsaClass }  -- constants, with default class
      | Free  { termBasicId  :: String, 
                termType     :: Typ, 
                defaultClass :: IsaClass }  -- free variables
      -- | Var   (Indexname, Typ)
      -- | Bound Int
      | Abs   { termId   :: Term, 
                termType :: Typ, 
                absVar   :: Term,
                flag     :: Flag }  -- lambda abstraction
      | App { funId :: Term, 
              argId :: Term, 
              flag  :: Flag }    -- application
      | Case { termId    :: Term, 
               caseSubst :: [(Term, Term)], 
               flag      :: Flag }  -- case
      | If { ifId   :: Term, 
             thenId :: Term, 
             elseId :: Term, 
             flag   :: Flag }        -- If then else
      | Let { letSubst :: [(Term, Term)], 
              inId     :: Term, 
              flag     :: Flag }   -- Let
      | Fix { funId    :: Term }
      deriving (Eq, Ord, Show)

data Sentence = Sentence { senTerm :: Term } deriving (Eq, Ord, Show) 


-------------------- from src/Pure/sorts.ML ------------------------

{-- type classes and sorts --}

{-
  Classes denote (possibly empty) collections of types that are
  partially ordered by class inclusion. They are represented
  symbolically by !!!!! strings. !!!!!!!!!!!

  Sorts are intersections of finitely many classes. They are
  represented by lists of classes.  Normal forms of sorts are sorted
  lists of minimal classes (wrt. current class inclusion).

  (already defined in Pure/term.ML)
-}


{- sort signature information -}

{-
  classrel:
    table representing the proper subclass relation; entries (c, cs)
    represent the superclasses cs of c;

  arities:
    table of association lists of all type arities; (t, ars) means
    that type constructor t has the arities ars; an element (c, Ss) of
    ars represents the arity t::(Ss)c;
-}

type Classrel = Map.Map IsaClass Sort
type Arities = Map.Map String [(IsaClass, [Sort])]


-------------------- from src/Pure/type.ML ------------------------

{- check what all the fields are. in particualar, check what arities
are in Isabelle and try to understand what role they play in the
translation. Then see whether there is some overlap with the new
definition of Sort.

emotional note -what the hell are all these strings?! 

maybe after all its better to use the new representation of Sort,
threfrom extracting the arities when needed. 
OK, add the HOLCF terms. 
What's Syntax?  

the problem now is to see where information about classes turns out
essential.  it is not clear whether we need to encode class
information explicitly in the term data-type. after all, classes
should be inferred by the type. anyway, its time to check the actual
translation. the most critical point seems to be beta-reduction -
that should actually produce proof obligations. -}

data TypeSig =
  TySg {
    classrel:: Classrel,  -- domain of the map yields the classes
    defaultSort:: Sort,
    log_types:: [String],
    univ_witness:: Maybe (Typ, Sort),
    abbrs:: Map.Map String ([String], Typ),
    arities:: Arities } -- the former field tycons can be computed 
   deriving (Eq, Show)

emptyTypeSig :: TypeSig
emptyTypeSig = TySg {
    classrel = Map.empty,
    defaultSort = [],
    log_types = [],
    univ_witness = Nothing,
    abbrs = Map.empty,
    arities = Map.empty }

-------------------- from src/Pure/sign.ML ------------------------

data Sign = Sign { baseSig :: String, -- like Pure, HOL, Main etc.
                   tsig :: TypeSig,
                   constTab :: Map.Map String Typ,  -- constants with type
                   dataTypeTab :: DataTypeTab,
                   domainTab :: DomainTab,  
                   -- needs HOLCF, extend this with domains
                   showLemmas :: Bool
                 }
             deriving (Eq, Show)

 {- list of datatype definitions
    each of these consists of a list of (mutually recursive) datatypes
    each datatype consists of its name (Typ) and a list of constructors
    each constructor consists of its name (String) and list of argument types
 -}                      
type DataTypeTab = [DataTypeTabEntry]
type DataTypeTabEntry = [(Typ,[DataTypeAlt])] -- (type,[constructors])
type DataTypeAlt = (String,[Typ])

type DomainTab = [DomainTabEntry]
type DomainTabEntry = [(Typ,[DomainAlt])] -- (type,[constructors])
type DomainAlt = (String,[Typ])

emptySign :: Sign
emptySign = Sign { baseSig = "Pure",
                   tsig = emptyTypeSig,
                   constTab = Map.empty,
                   dataTypeTab = [],
                   domainTab = [],
                   showLemmas = False }
