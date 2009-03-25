{- |
Module      :  $Header$
Description :  abstract Isabelle HOL and HOLCF syntax
Copyright   :  (c) University of Cambridge, Cambridge, England
               adaption (c) Till Mossakowski, Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Data structures for Isabelle signatures and theories.
   Adapted from Isabelle.
-}

module Isabelle.IsaSign where

import qualified Data.Map as Map
import Data.List

--------------- not quite from src/Pure/term.ML ------------------------
------------------------ Names -----------------------------------------

-- | type names
type TName = String

-- | names for values or constants (non-classes and non-types)
data VName = VName
    { new :: String -- ^ name within Isabelle
    , altSyn :: Maybe AltSyntax  -- ^ mixfix template syntax
    } deriving Show

data AltSyntax = AltSyntax String [Int] Int deriving Show

mkVName :: String -> VName
mkVName s = VName { new = s, altSyn = Nothing }

-- | the original (Haskell) name
orig :: VName -> String
orig = new

instance Eq VName where
    v1 == v2 = new v1 == new v2

instance Ord VName where
    v1 <= v2 = new v1 <= new v2

{- | Indexnames can be quickly renamed by adding an offset to
   the integer part, for resolution. -}
data Indexname = Indexname
    { unindexed :: String
    , indexOffset :: Int
    } deriving (Ord, Eq, Show)

{- Types are classified by sorts. -}

data IsaClass = IsaClass String deriving (Ord, Eq, Show)

type Sort = [IsaClass]

{- The sorts attached to TFrees and TVars specify the sort of
  that variable -}
data Typ = Type  { typeId    :: TName,
                   typeSort  :: Sort,
                   typeArgs  :: [Typ] }
         | TFree { typeId    :: TName,
                   typeSort  :: Sort }
         | TVar  { indexname :: Indexname,
                   typeSort  :: Sort }
         deriving (Eq, Ord, Show)

{- Terms.  Bound variables are indicated by depth number.
  Free variables, (scheme) variables and constants have names.
  A term is "closed" if every bound variable of level "lev"
  is enclosed by at least "lev" abstractions.

  It is possible to create meaningless terms containing loose bound vars
  or type mismatches.  But such terms are not allowed in rules. -}

-- IsCont True - lifted; IsCont False - not lifted, used for constructors
data Continuity = IsCont Bool | NotCont deriving (Eq, Ord, Show)

data TAttr = TFun | TMet | TCon | NA deriving (Eq, Ord, Show)

data DTyp = Hide { typ :: Typ,
                   kon :: TAttr,
                   arit :: Maybe Int }
          | Disp { typ :: Typ,
                   kon :: TAttr,
                   arit :: Maybe Int }
      deriving (Eq, Ord, Show)

data Term =
        Const { termName   :: VName,
                termType   :: DTyp }
      | Free  { termName     :: VName }
      | Abs   { absVar     :: Term,
                termId     :: Term,
                continuity :: Continuity }  -- lambda abstraction
      | App  { funId         :: Term,
               argId         :: Term,
               continuity    :: Continuity }    -- application
      | If { ifId   :: Term,
             thenId :: Term,
             elseId :: Term,
             continuity :: Continuity }
      | Case { termId      :: Term,
               caseSubst   :: [(Term, Term)] }
      | Let { letSubst       :: [(Term, Term)],
              inId           :: Term }
      | IsaEq { firstTerm  :: Term,
                secondTerm :: Term }
      | Tuplex [Term] Continuity
      | Set SetDecl
      deriving (Eq, Ord, Show)

data Sentence =
    Sentence { isSimp :: Bool   -- True for "[simp]"
             , isRefuteAux :: Bool
             , metaTerm :: MetaTerm
             , thmProof :: Maybe IsaProof }
  | Instance { tName :: TName
             , arityArgs :: [Sort]
             , arityRes :: Sort
             , instProof :: IsaProof }
  | ConstDef { senTerm :: Term }
  | RecDef { keyWord :: String
           , senTerms :: [[Term]] }
  | TypeDef { newType :: Typ
            , typeDef :: SetDecl
            , nonEmptyPr :: IsaProof}
    deriving (Eq, Ord, Show)

-- Other SetDecl variants to be added later
data SetDecl
    -- | Create a set using a subset. First parameter is the variable
    -- | Second is the type of the variable third is the formula
    -- | describing the set comprehension e.g. x Nat "even x" would be
    -- | produce the isabelle code: {x::Nat . even x}
    = SubSet Term Typ Term
    -- | A set declared using a list of terms. e.g. {1,2,3} would be Set [1,2,3]
    | FixedSet [Term]
               deriving (Eq, Ord, Show)

data MetaTerm = Term Term
              | Conditional [Term] Term -- List of preconditions, conclusion.
                deriving (Eq, Ord, Show)

mkSen :: Term -> Sentence
mkSen t = Sentence
    { isSimp = False
    , isRefuteAux = False
    , thmProof = Nothing
    , metaTerm = Term t }

mkCond :: [Term] -> Term -> Sentence
mkCond conds concl = Sentence
    { isSimp = False
    , isRefuteAux = False
    , thmProof = Nothing
    , metaTerm = Conditional conds concl}

mkRefuteSen :: Term -> Sentence
mkRefuteSen t = (mkSen t) { isRefuteAux = True }

isRefute :: Sentence -> Bool
isRefute s = case s of
    Sentence { isRefuteAux = b } -> b
    _ -> False

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
    deriving (Eq, Ord, Show)

emptyTypeSig :: TypeSig
emptyTypeSig = TySg {
    classrel = Map.empty,
    defaultSort = [],
    log_types = [],
    univ_witness = Nothing,
    abbrs = Map.empty,
    arities = Map.empty }

isSubTypeSig :: TypeSig -> TypeSig -> Bool
isSubTypeSig t1 t2 =
  null (defaultSort t1 \\ defaultSort t2) &&
  Map.isSubmapOf (classrel t1) (classrel t2) &&
  null (log_types t1 \\ log_types t2) &&
  (case univ_witness t1 of
     Nothing -> True
     w1 -> w1 == univ_witness t2) &&
  Map.isSubmapOf (abbrs t1) (abbrs t2) &&
  Map.isSubmapOf (arities t1) (arities t2)

-------------------- from src/Pure/sign.ML ------------------------

data BaseSig =
    Main_thy  -- ^ main theory of higher order logic (HOL)
  | MainHC_thy  -- ^ extend main theory of HOL logic for HasCASL
  | MainHCPairs_thy  -- ^ for HasCASL translation to bool pairs
  | HOLCF_thy   -- ^ higher order logic for continuous functions
  | HsHOLCF_thy  -- ^ HOLCF for Haskell
  | HsHOL_thy  -- ^ HOL for Haskell
  | MHsHOL_thy
  | MHsHOLCF_thy
  | CspHOLComplex_thy
    deriving (Eq, Ord, Show)
             {- possibly simply supply a theory like MainHC as string
                or recursively as Isabelle.Sign -}

data Sign = Sign
  { theoryName :: String
  , baseSig :: BaseSig -- like Main etc.
  , imports :: [String] -- additional imports
  , tsig :: TypeSig
  , constTab :: ConstTab  -- value cons with type
  , domainTab :: DomainTab
  , showLemmas :: Bool
  } deriving (Eq, Ord, Show)

 {- list of datatype definitions
    each of these consists of a list of (mutually recursive) datatypes
    each datatype consists of its name (Typ) and a list of constructors
    each constructor consists of its name (String) and list of argument
    types
 -}

type ConstTab = Map.Map VName Typ

-- same types for data types and domains

type DomainTab = [[DomainEntry]]
type DomainEntry = (Typ, [(VName, [Typ])])

emptySign :: Sign
emptySign = Sign
  { theoryName = "thy"
  , baseSig = Main_thy
  , imports = []
  , tsig = emptyTypeSig
  , constTab = Map.empty
  , domainTab = []
  , showLemmas = False }

isSubSign :: Sign -> Sign -> Bool
isSubSign s1 s2 =
    isSubTypeSig (tsig s1) (tsig s2) &&
    Map.isSubmapOf (constTab s1) (constTab s2) &&
    null (domainTab s1 \\ domainTab s2)

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

-- Data structures for Isabelle Proofs

data IsaProof = IsaProof
    { proof :: [ProofCommand],
      end :: ProofEnd
    } deriving (Show, Eq, Ord)

data ProofCommand
    -- | Apply a list of proof methods, which will be applied in sequence
    --    withing the apply proof command. The boolean is if the + modifier
    --    should be used at the end of the apply proof method. e.g. Apply(A,B,C)
    --    True would represent the Isabelle proof command "apply(A,B,C)+"
    = Apply [ProofMethod] Bool
    | Using [String]
    | Back
    | Defer Int
    | Prefer Int
    | Refute
      deriving (Show, Eq, Ord)

data ProofEnd
    = By ProofMethod
    | DotDot
    | Done
    | Oops
    | Sorry
      deriving (Show, Eq, Ord)

data Modifier
    -- | No_asm means that assumptions are completely ignored.
    = No_asm
    -- | No_asm_simp means that the assumptions are not simpliﬁed but
    -- | are used in the simpliﬁcation of the conclusion.
    | No_asm_simp
    -- | No_asm_use means that the assumptions are simpliﬁed but are
    -- | not used in the simpliﬁcation of each other or the
    -- | conclusion.
    | No_asm_use
      deriving (Show, Eq, Ord)

data ProofMethod
    -- | This is a plain auto with no parameters - it is used
    --   so often it warents its own constructor
    = Auto
    -- | This is a plain auto with no parameters - it is used
    --   so often it warents its own constructor
    | Simp
    -- | This is an auto where the simpset has been temporarily
    --   extended with a listof lemmas, theorems and axioms. An
    --   optional modifier can also be used to control how the
    --   assumptions are used. It is used so often it warents its own
    --   constructor
    | AutoSimpAdd (Maybe Modifier) [String]
    -- | This is a simp where the simpset has been temporarily
    --   extended with a listof lemmas, theorems and axioms.  An
    --   optional modifier can also be used to control how the
    --   assumptions are used. It is used so often it warents its own
    --   constructor
    | SimpAdd (Maybe Modifier) [String]
    -- | Induction proof method. This performs induction upon a variable
    | Induct Term
    -- |  Case_tac proof method. This perfom a case distinction on a term
    | CaseTac Term
    -- | Subgoal_tac proof method . Adds a term to the local
    --   assumptions and also creates a sub-goal of this term
    | SubgoalTac Term
    -- | Insert proof method. Inserts a lemma or theorem name to the assumptions
    --   of the first goal
    | Insert [String]
    -- | Used for proof methods that have not been implemented yet.
    --   This includes auto and simp with parameters
    | Other String
      deriving (Show, Eq, Ord)

toIsaProof :: ProofEnd -> IsaProof
toIsaProof e = IsaProof [] e

mkOops :: IsaProof
mkOops = toIsaProof Oops
