{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./OMDoc/DataTypes.hs
Description :  The OMDoc Data Types
Copyright   :  (c) Ewaryst Schulz, DFKI 2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  provisional
Portability :  portable

Datatypes for an intermediate OMDoc representation.
-}
module OMDoc.DataTypes where

import Common.Utils
import Common.Doc
import Common.DocUtils
import Common.Amalgamate (readShow)
import Common.Id
import Common.Lexer
import Common.AnnoParser
import Common.Percent (encodeBut)

import Data.List
import Data.Typeable

import qualified Data.Map as Map

{-
  OMDoc represented in 3 layers:
  1. toplevel (theory, view)
  2. theory constitutive (axiom, symbol)
  3. subelements (insort, ...) and OpenMath
-}


-- -------------------- Datatypes for Representation ----------------------


-- | OMDoc root element with libname and a list of toplevel elements
data OMDoc = OMDoc String [TLElement] deriving (Show, Read, Eq, Ord)

{- | Toplevel elements for OMDoc, theory with name, meta and content,
view with from, to and morphism -}
data TLElement = TLTheory String (Maybe OMCD) [TCElement]
               | TLView String OMCD OMCD TCMorphism
                 deriving (Show, Read, Eq, Ord)

{-
 NOTATIONS

OMDoc currently supports two kinds of notations: smart and flexible.

a) The smart ones look like this:

<notation for="??+" role="application" fixity="f" precedence="p" implicit="i"/>

Here f \in {in, pre, post}, p is an integer (higher precedence =
higher binding), and i is the number of implicit arguments (0 by
default).

In this case, you would additionally give
 <notation for="??+" role="constant"><text value="+"/></notation>
This notation is called to render operation itself, i.e.,
produces the operator symbol.

b) The flexible ones look like this

<notation for="??something" role="application" precedence="P">
 <component index="1" precedence="p1"/>
 <text value="["/>
 <component index="2" precedence="p2"/>
 <text value="/"/>
 <component index="3" precedence="p3"/>
 <text value="]"/>
</notation>

Here <component index="i"/> recurses into argument number i.
P is the output precedence, p1,p2,p3 are the input precedences.

You can also use <component index="0"/>. That renders the operator
symbol by calling the notation
 <notation for="??+" role="constant">...</notation>

2) The smart ones have two major advantages:
  - They can be read back easily.
  - They are independent of the output format.
In 1b) above, we would need one notation for Hets-syntax, one for MathML etc
-}

-- | Theory constitutive elements for OMDoc
data TCElement =
    -- | Symbol to represent sorts, constants, predicate symbols, etc.
    TCSymbol String OMElement SymbolRole (Maybe OMElement)
    -- | A notation for the given symbol with an optional style
  | TCNotation OMQualName String (Maybe String)
    {- | A smart notation for the given symbol with fixity, associativity,
    precedence and the number of implicit arguments -}
  | TCSmartNotation OMQualName Fixity Assoc Int Int
    {- | A smart notation for the given symbol, the argument- and
    text-components have to alternate in the component list -}
  | TCFlexibleNotation OMQualName Int [NotationComponent]
    -- | Algebraic Data Type represents free/generated types
  | TCADT [OmdADT]
    -- | Import statements for referencing other theories
  | TCImport String OMCD TCMorphism
    -- | A comment, only for development purposes
  | TCComment String
    deriving (Show, Read, Eq, Ord)

-- | return type for sentence translation (ADT or formula)
type TCorOMElement = Either TCElement OMElement

-- | Morphisms to specify signature mappings
type TCMorphism = [(OMName, OMImage)]

{- | The target type of a mapping is just an alias or an assignment to
a symbol -}
type OMImage = Either String OMElement

-- | The flattened structure of an Algebraic Data Type
data OmdADT =
    -- | A single sort given by name, type and a list of constructors
    ADTSortDef String ADTType [OmdADT]
    -- | A constructor given by its name and a list of arguments
  | ADTConstr String [OmdADT]
    -- | An argument with type and evtually a selector
  | ADTArg OMElement (Maybe OmdADT)
    -- | The selector has a name and is total (Yes) or partial (No)
  | ADTSelector String Totality
    -- | Insort elements point to other sortdefs and inherit their structure
  | ADTInsort OMQualName
    deriving (Show, Read, Eq, Ord)

-- | Roles of the declared symbols can be object or type
data SymbolRole = Obj | Typ | Axiom | Theorem deriving (Eq, Ord)

-- | Fixity of notation patterns
data Fixity = Infix | Prefix | Postfix deriving (Eq, Ord)

-- | Associativity of notation patterns
data Assoc = LeftAssoc | RightAssoc | NoneAssoc deriving (Eq, Ord)

-- | Type of the algebraic data type
data ADTType = Free | Generated deriving (Eq, Ord)

-- | Totality for selectors of an adt
data Totality = Yes | No deriving (Eq, Ord)

{- | A component can be a text-component, e.g., <text value="["/>, or an
argument-component such as <component index="1" precedence="p1"/> -}
data NotationComponent = TextComp String | ArgComp Int Int
    deriving (Show, Read, Eq, Ord)


instance Show SymbolRole where
    show Obj = "object"
    show Typ = "type"
    show Axiom = "axiom"
    show Theorem = "theorem"

instance Show ADTType where
    show Free = "free"
    show Generated = "generated"

instance Show Totality where
    show Yes = "yes"
    show No = "no"

instance Show Fixity where
    show Infix = "in"
    show Prefix = "pre"
    show Postfix = "post"

instance Show Assoc where
    show LeftAssoc = "left"
    show RightAssoc = "right"
    show NoneAssoc = "none"

instance Read SymbolRole where
    readsPrec _ = readShow [Obj, Typ, Axiom, Theorem]

instance Read ADTType where
    readsPrec _ = readShow [Free, Generated]

instance Read Totality where
    readsPrec _ = readShow [Yes, No]

instance Read Fixity where
    readsPrec _ = readShow [Infix, Prefix, Postfix]

instance Read Assoc where
    readsPrec _ = readShow [LeftAssoc, RightAssoc, NoneAssoc]

-- | Names used for OpenMath variables and symbols
data OMName = OMName { name :: String, path :: [String] }
              deriving (Show, Read, Eq, Ord, Typeable)

{- | Attribute-name/attribute-value pair used to represent the type
of a type-annotated term -}
data OMAttribute = OMAttr OMElement OMElement
                      deriving (Show, Read, Eq, Ord)

{- | CD contains the reference to the content dictionary
and eventually the cdbase entry -}
data OMCD = CD [String] deriving (Show, Read, Eq, Ord)

type OMQualName = (OMCD, OMName)

-- | Elements for Open Math
data OMElement =
    -- | Symbol
    OMS OMQualName
    -- | Simple variable
  | OMV OMName
    -- | Attributed element needed for type annotations of elements
  | OMATTT OMElement OMAttribute
    {- | Application to a list of arguments,
    first argument is usually the functionhead -}
  | OMA [OMElement]
    -- | Bindersymbol, bound vars, body
  | OMBIND OMElement [OMElement] OMElement
  deriving (Show, Read, Eq, Ord)


-- * Hets Utils

nameToId :: String -> Id
nameToId = parseString parseAnnoId

nameToToken :: String -> Token
nameToToken = mkSimpleId

-- * Utils for Translation

type UniqName = (String, Int)
type NameMap a = Map.Map a UniqName

-- | Mapping of symbols and sentence names to unique ids (used in export)
data SigMap a = SigMap (NameMap a) (NameMap String)

{- | Mapping of OMDoc names to hets strings, for signature creation,
and strings to symbols, for lookup in terms (used in import) -}
data SigMapI a = SigMapI { sigMapISymbs :: Map.Map OMName a
                         , sigMapINotations :: Map.Map OMName String }

sigMapSymbs :: SigMap a -> NameMap a
sigMapSymbs (SigMap sm _) = sm

cdFromList :: [String] -> OMCD
cdFromList ["", ""] = CD []
cdFromList ["", cd] = CD [cd]
cdFromList [base, cd] = CD [cd, base]
cdFromList _ = error "cdFromList: Malformed list. I need exactly 2 elements!"

cdIsEmpty :: OMCD -> Bool
cdIsEmpty cd = ["", ""] == cdToList cd

-- | The result list has always two elements: [base, modul]
cdToList :: OMCD -> [String]
cdToList (CD [cd, base]) = [base, cd]
cdToList (CD [cd]) = ["", cd]
cdToList _ = ["", ""]

cdToMaybeList :: OMCD -> [Maybe String]
cdToMaybeList (CD [cd, base]) = [Just base, Just cd]
cdToMaybeList (CD [cd]) = [Nothing, Just cd]
cdToMaybeList _ = [Nothing, Nothing]


-- * Name handling: encoding, decoding, unique names

{- | The closing paren + percent can be used neither in ordinary Hets-names
nor in sentence names hence it is used here for encodings. -}
uniqPrefix :: String
uniqPrefix = "%()%"

{- | Special name encoding in order to be able to recognize these names
while reading. -}
nameEncode :: String -- ^ the kind of the encoding, may not contain colons
           -> [String] -- ^ the values to encode
           -> String
nameEncode s l = concat [uniqPrefix, s, ":", intercalate uniqPrefix l]

{- | This invariant should hold:
@(x, l) = fromJust $ nameDecode $ nameEncode x l@ -}
nameDecode :: String -> Maybe (String, [String])
nameDecode s =
    case stripPrefix uniqPrefix s of
      Nothing -> Nothing
      Just s' ->
          let (kind, r) = break (== ':') s'
          in if null r
             then error $ "nameDecode: missing colon in " ++ s
             else Just (kind, splitByList uniqPrefix $ tail r)

nameToString :: UniqName -> String
nameToString (s, i) =
    let s' = encodeBut (`notElem` "/?%#") s
    in if i > 0 then nameEncode ("over_" ++ show i) [s'] else s'

-- * Constructing/Extracting Values

{- | name of the theory constitutive element, error if not TCSymbol, TCNotation,
or TCImport -}
tcName :: TCElement -> OMName
tcName tc = case tc of
              TCSymbol s _ _ _ -> mkSimpleName s
              TCNotation qn _ _ -> unqualName qn
              TCImport s _ _ -> mkSimpleName s
              _ -> error "tcName: No name for this value."

unqualName :: OMQualName -> OMName
unqualName = snd


emptyCD :: OMCD
emptyCD = CD []

omName :: UniqName -> OMName
omName = mkSimpleName . nameToString

mkSimpleName :: String -> OMName
mkSimpleName s = OMName s []

mkSimpleQualName :: UniqName -> OMQualName
mkSimpleQualName un = (CD [], omName un)

simpleOMS :: UniqName -> OMElement
simpleOMS = OMS . mkSimpleQualName

-- * Lookup utils for Import and Export

lookupNotation :: SigMapI a -> OMName -> String
lookupNotation smi = lookupNotationInMap $ sigMapINotations smi

lookupNotationInMap :: Map.Map OMName String -> OMName -> String
lookupNotationInMap m n = Map.findWithDefault (name n) n m

-- * Pretty instances

instance Pretty OMName where
    pretty = text . show
