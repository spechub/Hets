 {- list of datatype definitions
    each of these consists of a list of (mututally recursive) datatypes
    each datatype consists of its name (Typ) and a list of constructors
    each constructor consists of its name (String) and list of argument types
 -}                      
{- |
Module      :  $Header$
Copyright   :  (c) University of Cambridge, Cambridge, England
               adaption (c) Till Mossakowski, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   Data structures for Isabelle sigantures and theories.
   Adapted from Isabelle.
-}

module Isabelle.IsaSign where

import qualified Common.Lib.Map as Map

---------------- from src/Pure/Syntax/syntax.ML -------------------

type Syntax = () -- leave this for later

-- temporary!!
type Axiom = ()
-- type ProofObl = ()

-------------------- from src/Pure/term.ML ------------------------

{-Indexnames can be quickly renamed by adding an offset to the integer part,
  for resolution.-}
type Indexname = (String,Int)

{- Types are classified by sorts. -}

-- Classes

data IsaClass  = IsaClass { classId :: String, classDef :: [Axiom] }
              | ClFun IsaClass IsaClass          
              deriving (Ord, Eq, Show)   

--instance PPrint IsaClass where
--   pprint (IsaClass c _) = text "(" <> text c <> text ")"
--   pprint (ClFun c1 c2) =   
--           text "(" <> pprint c1 <> text ")->(" <> pprint c2 <> text ")"

type Sort  = [IsaClass]

domain:: Sort
domain = [pcpo]

isaTerm :: IsaClass
isaTerm = IsaClass "term" []

holType :: IsaClass
holType = IsaClass "hol_type" []

pcpo :: IsaClass
pcpo = IsaClass "pcpo" []

ho_ho_ho :: IsaClass  -- (hol_type,hol_type)hol_type
ho_ho_ho = ClFun holType (ClFun holType holType)


------------------------------------------------------------------------------

{- The sorts attached to TFrees and TVars specify the sort of that variable -}
data Typ = Type  { typeId   :: String,
                   typeSort :: Sort,
                   typeArg  :: [Typ] } 
         | TFree { typeId    :: String,
                   typeSort  :: Sort}
         | TVar  { indexname :: Indexname, -- (String,Int)
                   typeSort  :: Sort }
         deriving (Eq, Ord)

noType :: Typ
noType = dummyT

dummyT :: Typ
dummyT = Type "dummy" [holType] []

boolType :: Typ
boolType = Type "bool" [holType] []

mkOptionType :: Typ -> Typ
mkOptionType t = Type "option" [holType] [t]

mkProductType :: Typ -> Typ -> Typ
mkProductType t1 t2 = Type "*" [ho_ho_ho] [t1,t2]

mkTypeAppl :: Typ -> Typ -> Typ
mkTypeAppl t1 t2 = Type "typeAppl" [ho_ho_ho] [t1,t2]

mkFunType :: Typ -> Typ -> Typ
mkFunType s t = Type "fun" [ho_ho_ho] [s,t] -- was "-->" before

{-handy for multiple args: [T1,...,Tn]--->T  gives  T1-->(T2--> ... -->T)-}
mkCurryFunType :: [Typ] -> Typ -> Typ
mkCurryFunType = flip $ foldr mkFunType -- was "--->" before

voidDom :: Typ
voidDom = Type "void" domain []
-- voidDom = Type ("void",[pcpo],[])

{- should this be included (as primitive)? -}
flatDom :: Typ
flatDom = Type "flat" domain []

{- sort is ok? -}
mkContFun :: Typ -> Typ -> Typ
mkContFun t1 t2 = Type "dFun" domain [t1,t2]
-- mkContFun = Type ("dFun", [cp_pc_pc],[s,t])

mkDomProduct :: Typ -> Typ -> Typ
mkDomProduct t1 t2 = Type "**" domain [t1,t2]
-- mkDomProduct t1 t2 = Type ("**",[pc_pc_pc],[t1,t2])

mkDomSum :: Typ -> Typ -> Typ
mkDomSum t1 t2 = Type "++" domain [t1,t2]
-- mkDomSum t1 t2 = Type ("++",[pc_pc_pc],[t1,t2])

{- type application. is the sort ok? -}
mkDomAppl :: Typ -> Typ -> Typ 
mkDomAppl t1 t2 = Type "domAppl" domain [t1,t2]
-- mkDomAppl t1 t2 = 
--      Type ("domAppl",[pc_pc_pc],[t1,t2])


{-Terms.  Bound variables are indicated by depth number.
  Free variables, (scheme) variables and constants have names.
  A term is "closed" if every bound variable of level "lev"
  is enclosed by at least "lev" abstractions.

  It is possible to create meaningless terms containing loose bound vars
  or type mismatches.  But such terms are not allowed in rules. -}

data Flag = IsCont | NotCont deriving (Eq,Ord)

data Term =
        Const { termBasicId::String, 
                termType::Typ, 
                defaultClass::IsaClass }  -- constants, with default class
      | Free  { termBasicId::String, 
                termType::Typ, 
                defaultClass::IsaClass }  -- free variables
      -- | Var   (Indexname, Typ)
      -- | Bound Int
      | Abs   { termId::Term, 
                termType::Typ, 
                absVar::Term,
                flag::Flag }  -- lambda abstraction
--      | CAbs   { termId::Term, 
--                termType::Typ, 
--                absVar::Term }  -- lambda abstraction
      | App { funId::Term, 
              argId::Term, 
              flag::Flag }    -- application
--      | CApp { funId::Term, argId::Term } -- application
      | Case { termId::Term, caseSubst::[(Term, Term)], flag::Flag }  -- case
      | If { ifId::Term, 
             thenId::Term, 
             elseId::Term, 
             flag::Flag }        -- If then else
      | Let { letSubst::[(Term, Term)], 
              inId::Term, 
              flag::Flag }   -- Let
      | Fix { funId::Term }
      deriving (Eq, Ord)

--      | CApp { funId::Term, termId::Term, proofObl::ProofObl } -- application

data Sentence = Sentence { senTerm :: Term } deriving (Eq, Ord) 


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

type Classrel = Map.Map String [IsaClass]
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
    classes:: [IsaClass],
    classrel:: Classrel,
    defaultSort:: Sort,
    tycons:: Map.Map String Int,  -- type constructor names, with arities
    log_types:: [String],
    univ_witness:: Maybe (Typ, Sort),
    abbrs:: Map.Map String ([String], Typ),
    arities:: Arities }
   deriving (Eq)

emptyTypeSig :: TypeSig
emptyTypeSig = TySg {
    classes = [],
    classrel = Map.empty,
    defaultSort = [],
    tycons = Map.empty,
    log_types = [],
    univ_witness = Nothing,
    abbrs = Map.empty,
    arities = Map.empty }

-------------------- from src/Pure/sign.ML ------------------------

data Sign = Sign { baseSig :: String, -- like Pure, HOL, Main etc.
                   tsig :: TypeSig,
                   constTab :: Map.Map String Typ,  -- constants with type
                   dataTypeTab :: DataTypeTab,
                   domainTab :: DomainTab,  -- needs HOLCF, extend this with domains
                   syn :: Syntax,
                   showLemmas :: Bool
                 }
             deriving (Eq)

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
                   showLemmas = False,
                   syn = () }
