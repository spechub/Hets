{- |
Module      :  $Header$
Copyright   :  (c) University of Cambridge, Cambridge, England
               adaption (c) Till Mossakowski, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

Data structures for Isabelle signatures and theories.
   Adapted from Isabelle.

LogicList.hs
LogicGraph.hs

-}

module Isabelle.IsaSign where

import qualified Common.Lib.Map as Map

-------------------- not quite from src/Pure/term.ML ------------------------
----------------------------- Names -----------------------------------------

type IName = String

type CName = IName  -- class name
type TName = IName  -- type name
type VName = IName -- value name

{-Indexnames can be quickly renamed by adding an offset to the integer part,
  for resolution.-}
type Indexname = (String,Int)

--------- Classes
{- Types are classified by sorts. -}

data IsaClass  = IsaClass {classId :: CName}
                 deriving (Ord, Eq, Show)   

type Sort  = [IsaClass]

holType :: Sort
holType = [IsaClass "hol_type"]

dom:: Sort
dom = [pcpo]

isaTerm :: IsaClass
isaTerm = IsaClass "type"

pcpo :: IsaClass
pcpo = IsaClass "pcpo"


----------- Kinds

data ExKind = IKind IsaKind | IClass | PLogic

data IsaKind  = Star
              | Kfun IsaKind IsaKind
                deriving (Ord, Eq, Show)  

------------------------------------------------------------------------------

{- The sorts attached to TFrees and TVars specify the sort of that variable -}
data Typ = Type  { typeId    :: TName,
                   typeSort  :: Sort,
                   typeArgs  :: [Typ] } 
         | TFree { typeId    :: TName,
                   typeSort  :: Sort }
         | TVar  { indexname :: Indexname, -- (String,Int)
                   typeSort  :: Sort }
         deriving (Eq, Ord, Show)

typeAppl :: Typ -> [Typ] -> Typ
typeAppl t ts = 
 case ts of 
   [] -> t
   v:vs -> typeAppl (binTypeAppl t v) vs

binTypeAppl :: Typ -> Typ -> Typ
binTypeAppl t1 t2 = case t1 of
    Type n s ts -> Type n s (t2:ts) 
    _ -> error "IsaSign.binTypeAppl, unsupported type application"                 
noType :: Typ
noType = dummyT

dummyT :: Typ
dummyT = Type "dummy" holType []

boolType :: Typ
boolType = Type "bool" holType []

mkOptionType :: Typ -> Typ
mkOptionType t = Type "option" holType [t]

prodType :: Typ -> Typ -> Typ
prodType t1 t2 = Type prodS holType [t1,t2]

mkFunType :: Typ -> Typ -> Typ
mkFunType s t = Type funS holType [s,t] -- was "-->" before

{-handy for multiple args: [T1,...,Tn]--->T  gives  T1-->(T2--> ... -->T)-}
mkCurryFunType :: [Typ] -> Typ -> Typ
mkCurryFunType = flip $ foldr mkFunType -- was "--->" before

voidDom :: Typ
voidDom = Type "void" dom []
-- voidDom = Type ("void",[pcpo],[])

{- should this be included (as primitive)? -}
flatDom :: Typ
flatDom = Type "flat" dom []

{- sort is ok? -}
mkContFun :: Typ -> Typ -> Typ
mkContFun t1 t2 = Type "dFun" dom [t1,t2]

mkStrictProduct :: Typ -> Typ -> Typ
mkStrictProduct t1 t2 = Type "**" dom [t1,t2]

mkContProduct :: Typ -> Typ -> Typ
mkContProduct t1 t2 = Type "*" dom [t1,t2]

{-handy for multiple args: [T1,...,Tn]--->T  gives  T1-->(T2--> ... -->T)-}
mkCurryContFun :: [Typ] -> Typ -> Typ
mkCurryContFun = flip $ foldr mkContFun -- was "--->" before

mkStrictSum :: Typ -> Typ -> Typ
mkStrictSum t1 t2 = Type "++" dom [t1,t2]

prodS :: TName
prodS = "*"    -- this is printed as it is!

funS :: TName 
funS = "fun"  -- may be this should be "=>" for printing

{-Terms.  Bound variables are indicated by depth number.
  Free variables, (scheme) variables and constants have names.
  A term is "closed" if every bound variable of level "lev"
  is enclosed by at least "lev" abstractions.

  It is possible to create meaningless terms containing loose bound vars
  or type mismatches.  But such terms are not allowed in rules. -}

data Continuity = IsCont | NotCont deriving (Eq, Ord ,Show)

data Term =
        Const { termName     :: VName,
                termType     :: Typ } 
      | Free  { termName   :: VName,  
                termType     :: Typ } 
      | Var  Indexname Typ
      | Bound Int
      | Abs   { absVar     :: Term,
                termType   :: Typ, 
                termId     :: Term, 
                continuity :: Continuity }  -- lambda abstraction
      | App  { funId :: Term, 
               argId :: Term, 
               continuity   :: Continuity }    -- application
      | If { ifId   :: Term, 
             thenId :: Term, 
             elseId :: Term,
             continuity :: Continuity } 
      | Case { termId       :: Term, 
               caseSubst    :: [(Term, Term)] } 
      | Let { letSubst    :: [(Term, Term)], 
              inId        :: Term } 
      | IsaEq { firstTerm  :: Term,
                secondTerm :: Term }
      | Tuplex [Term] Continuity 
      | Fix Term 
      | Bottom 
      | Paren Term
      | Wildcard
      deriving (Eq, Ord, Show)

data Sentence = Sentence { senTerm :: Term } -- axiom
              | Theorem { thmFlag :: Bool  -- True for "theorem"
                        , senTerm :: Term 
                        , thmProof :: Maybe String }
              | ConstDef { senTerm :: Term }
              | RecDef { keyWord :: String 
                       , senTerms :: [[Term]] }
                deriving (Eq, Ord, Show)

-------------------- from src/Pure/sorts.ML ------------------------

{-- type classes and sorts --}

{-  Classes denote (possibly empty) collections of types that are
  partially ordered by class inclusion. They are represented
  symbolically by strings. 

  Sorts are intersections of finitely many classes. They are
  represented by lists of classes.  Normal forms of sorts are sorted
  lists of minimal classes (wrt. current class inclusion).

  (already defined in Pure/term.ML)

  classrel:
    table representing the proper subclass relation; entries (c, cs)
    represent the superclasses cs of c;

  arities:
    table of association lists of all type arities; (t, ars) means
    that type constructor t has the arities ars; an element (c, Ss) of
    ars represents the arity t::(Ss)c;
-}

type Classrel = Map.Map IsaClass (Maybe [IsaClass])
type Arities = Map.Map TName [(IsaClass, [(Typ, Sort)])]
type Abbrs = Map.Map TName ([TName], Typ)

data TypeSig =
  TySg {
    classrel:: Classrel,  -- domain of the map yields the classes
    defaultSort:: Sort,
    log_types:: [TName],
    univ_witness:: Maybe (Typ, Sort),
    abbrs:: Abbrs, -- constructor name, variable names, type.
    arities:: Arities } 
    -- actually isa-instances. the former field tycons can be computed.
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

data BaseSig = Pure_thy | HOL_thy | HOLCF_thy | Main_thy | MainHC_thy | HsHOLCF_thy
             deriving (Eq, Ord, Show) 
             {- possibly simply supply a theory like MainHC as string 
                or recursively as Isabelle.Sign -}

data Sign = Sign { baseSig :: BaseSig, -- like Pure, HOL, Main etc.
                   tsig :: TypeSig,
                   constTab :: ConstTab,  -- value cons with type
                   domainTab :: DomainTab,  
                   dataTypeTab :: DataTypeTab,
                   showLemmas :: Bool
                 }
             deriving (Eq, Show)

 {- list of datatype definitions
    each of these consists of a list of (mutually recursive) datatypes
    each datatype consists of its name (Typ) and a list of constructors
    each constructor consists of its name (String) and list of argument types
 -}                      

type ConstTab = Map.Map VName Typ

type DataTypeTab = [DataTypeTabEntry]
type DataTypeTabEntry = [DataTypeEntry] -- (type,[value cons])
type DataTypeEntry = (Typ,[DataTypeAlt])
type DataTypeAlt = (VName,[Typ])

type DomainTab = [DomainTabEntry]
type DomainTabEntry = [DomainEntry] -- (type,[value cons])
type DomainEntry = (Typ,[DomainAlt])
type DomainAlt = (VName,[Typ])

emptySign :: Sign
emptySign = Sign { baseSig = Pure_thy,
                   tsig = emptyTypeSig,
                   constTab = Map.empty,
                   dataTypeTab = [],
                   domainTab = [],
                   showLemmas = False }

------------------------ Sentence -------------------------------------

{- Instances in Haskell have form:

instance (MyClass a, MyClass b) => MyClass (MyTypeConst a b)

In Isabelle:

instance MyTypeConst :: (MyClass, MyClass) MyClass

Note that the Isabelle syntax does not allows for multi-parameter classes.
Rather, it subsumes the syntax for arities.

Type constraints are applied to value constructors in Haskell as follows:

MyValCon :: (MyClass a, MyClass b) => MyTypeConst a b

In Isabelle:

MyValCon :: MyTypeConst (a::MyClass) (b::MyClass)

In both cases, the typing expressions may be encoded as schemes.
Schemes and instances allows for the inference of type constraints over 
values of functions.
-}
