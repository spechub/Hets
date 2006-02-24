{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

document data type for displaying (heterogenous) CASL specifications
at least as plain text and latex (and maybe in html as well)

inspired by John Hughes's and Simon Peyton Jones's Pretty Printer Combinators
in 'Text.PrettyPrint.HughesPJ' and Thomas Hallgren's
<http://www.cse.ogi.edu/~hallgren/Programatica/tools/pfe.cgi?PrettyDoc>
-}

module Common.Doc
    ( -- * The document type
      Doc            -- Abstract
      -- * Primitive Documents
    , empty
    , space
    , semi
    , comma
    , colon
    , equals
    , lparen
    , rparen
    , lbrack
    , rbrack
    , lbrace
    , rbrace
      -- * Converting values into documents
    , text
      -- * Wrapping documents in delimiters
    , parens
    , brackets
    , braces
    , quotes
    , doubleQuotes
      -- * Combining documents
    , (<>)
    , (<+>)
    , hcat
    , hsep
    , ($+$)
    , vcat
    , sep
    , cat
    , fsep
    , fcat
    , punctuate
    , indentBy
      -- * keywords
    , keyword
    , topKey
    , indexed
    , structId
      -- * symbols
    , dot
    , bullet
    , defn
    , less
    , lambda
    , mapsto
    , rightArrow
    , pfun
    , cfun
    , pcfun
    , exequal
    , forallDoc
    , exists
    , unique
    , cross
    , bar
    , notDoc
    , inDoc
    , andDoc
    , orDoc
    , implies
    , equiv
      -- * docifying annotations and ids
    , annoDoc
    , idDoc
    , idApplDoc
    ) where

import Common.Id
import Common.AS_Annotation

infixl 6 <>
infixl 6 <+>
infixl 5 $+$

{-
data Format = Proportional | Bold | Italic | SmallCaps | Plain -- Fixed size

-- font size
data Size = Size Int -- 0 = normal, 1 = large, ..., 5 = Huge
                        -- -1 = small, ..., -4 = tiny

data Justification = FlushLeft | Center | FlushRight
-}

data TextKind = IdKind | Keyword | TopKey | Indexed | StructId

data ComposeKind
    = Vert   -- ($+$) (no support for $$!)
    | Horiz  -- (<>)
    | HorizOrVert -- either Horiz or Vert
    | Fill

data Doc
    = Empty -- creates an empty line if composed vertically
    | AnnoDoc Annotation -- we know how to print annotations
    | IdDoc Id           -- for plain ids outside applications
    | IdApplDoc Id [Doc] -- for mixfix applications and literal terms
    | Space
      {- a blank if composed horizontally, ignored in vertical
      compositions -}
    | Text TextKind String -- non-empty and no white spaces inside
    | Symbol String        -- CASL symbols
    | Cat ComposeKind [Doc]
{-
    | Formatted Format Doc
    | Sized Size Doc
    | FlushRight Doc
    | UseFont String Doc -- a font named by a string
-}
    | IndentBy Doc Doc Doc

{-
IdentBy refDoc startDoc hangDoc

is: startDoc <> (length refDoc - length startDoc) <> hangDoc
if refDoc >= startDoc
    (i.e indent hangBlock by refDoc and put it beside startDoc)

is: startDoc <> hangDoc if it fits on a single line!
is: startDoc $+$
       nest refDoc hangDoc
if refDoc < startDoc

Another indentation mode we might want to have is:
  hangedFill :: Doc -> [Doc] -> Doc with
  hangedFill refDoc [d1, ..., dn]

   put as many ds on a line that fit, but indent further lines by the
   width of refDoc.

Maybe one even wants a negative refDoc, if
   hangedFill happens to start farther to the right:

   keyw "longone" <+> hangFill (- (text "one")) ds
   = hangedFill (text "long") $ keyw "longone" <> space) : ds
-}

isEmpty :: Doc -> Bool
isEmpty d = case d of
              Empty -> True
              _ -> False

empty :: Doc                 -- ^ An empty document
empty = Empty

text :: String -> Doc
text = Text IdKind

semi :: Doc                 -- ^ A ';' character
semi = text ";"

comma :: Doc                 -- ^ A ',' character
comma = text ","

colon :: Doc                 -- ^ A ':' character
colon = text ":"

space :: Doc                 -- ^ A horizontal space (omitted at end of line)
space = Space

equals :: Doc                 -- ^ A '=' character
equals = text "="

lparen, rparen, lbrack, rbrack, lbrace, rbrace, quote, doubleQuote :: Doc

lparen = text "("
rparen = text ")"
lbrack = text "["
rbrack = text "]"
lbrace = text "{"
rbrace = text "}"
quote = text "\'"
doubleQuote = text "\""

parens :: Doc -> Doc     -- ^ Wrap document in @(...)@
parens d = fcat [lparen, d, rparen]

brackets :: Doc -> Doc     -- ^ Wrap document in @[...]@
brackets d = fcat [lbrack, d, rbrack]

braces :: Doc -> Doc     -- ^ Wrap document in @{...}@
braces d = cat [lbrace <> d, rbrace]

quotes :: Doc -> Doc     -- ^ Wrap document in @\'...\'@
quotes d = hcat [quote, d, quote]

doubleQuotes :: Doc -> Doc     -- ^ Wrap document in @\"...\"@
doubleQuotes d = hcat [doubleQuote, d, doubleQuote]

(<>) :: Doc -> Doc -> Doc      -- ^Beside
a <> b = Cat Horiz [a, b]

hcat :: [Doc] -> Doc          -- ^List version of '<>'
hcat = Cat Horiz

(<+>) :: Doc -> Doc -> Doc     -- ^Beside, separated by space
a <+> b = if isEmpty a then b else
          if isEmpty b then a else Cat Horiz [a, space, b]

punctuate :: Doc -> [Doc] -> [Doc]
punctuate d l = case l of
     x : r@(_ : _) -> (x <> d) : punctuate d r
     _ -> l

hsep :: [Doc] -> Doc         -- ^List version of '<+>'
hsep = hcat . punctuate space

($+$) :: Doc -> Doc -> Doc;    -- ^Above, without dovetailing.
a $+$ b = Cat Vert [a, b]

vcat :: [Doc] -> Doc          -- ^List version of '$+$'
vcat = Cat Vert

cat    :: [Doc] -> Doc          -- ^ Either hcat or vcat
cat = Cat HorizOrVert

sep    :: [Doc] -> Doc          -- ^ Either hsep or vcat
sep = cat . punctuate space

fcat   :: [Doc] -> Doc          -- ^ \"Paragraph fill\" version of cat
fcat = Cat Fill

fsep   :: [Doc] -> Doc          -- ^ \"Paragraph fill\" version of sep
fsep = fcat . punctuate space

keyword, topKey, indexed, structId :: String -> Doc
keyword = Text Keyword
indexed = Text Indexed
structId = Text StructId
topKey = Text TopKey

-- | docs possibly rendered differently for Text or LaTeX
dot, bullet, defn, less, lambda, mapsto, rightArrow, pfun, cfun, pcfun,
   exequal, forallDoc, exists, unique, cross, bar, notDoc, inDoc, andDoc,
   orDoc, implies, equiv :: Doc

dot = text "."
bullet = Symbol "."
defn = Symbol "::="
less = text "<"
lambda = Symbol "lambda"
mapsto = Symbol "|->"
rightArrow = Symbol "->"
pfun = Symbol "->?"
cfun = Symbol "-->"
pcfun = Symbol "-->?"
exequal = Symbol "=e="
forallDoc = Symbol "forall"
exists = Symbol "exists"
unique = Symbol "exists!"
cross = Symbol "*"
bar = Symbol "|"
notDoc = Symbol "not"
inDoc = Symbol "in"
andDoc = Symbol "/\\"
orDoc = Symbol "\\/"
implies = Symbol "=>"
equiv = Symbol "<=>"

-- | we know how to print annotations
annoDoc :: Annotation -> Doc
annoDoc = AnnoDoc

-- | for plain ids outside applications
idDoc :: Id -> Doc
idDoc = IdDoc

-- | for mixfix applications and literal terms (may print \"\" for empty)
idApplDoc :: Id -> [Doc] -> Doc
idApplDoc = IdApplDoc

{- | print second argument and then indent the last one by the width
of the first one -}

indentBy :: Doc -> Doc -> Doc -> Doc
indentBy = IndentBy

{-

All key signs:

non-formula key signs: : :? ::= . | |-> -> ->? * ? < = <=>

(treat = and <=> in OP- and PRED-DEFN like formulas)

(<, = may appear following sort, = also used for SPEC-DEFN, etc. )
( : in UNIT- and VIEW-DEFNs)

extra/formula key signs: forall exists exists! in lambda (+, -> in USP)

formula/term identifiers: not__ __=__ __=>__ __=e=__ __<=>__ __/\__ __\/__
possibly user defined:          < * ? -> ->? ! (and |)

implicit latex display annotation for "not__"? (also for "__in__"?)


Keywords:

toplevel basic item keywords:
 sort op pred type free generated var forall axiom .

formula keywords: as in when else if def not false true

attributes: assoc comm idem unit (also in archs)

toplevel spec keywords: free local closed cofree logic data arch( spec) unit(s)
   behaviourally refined
infix spec keywords followed by symbols: with hide reveal fit
infix spec keywords followed by spec: and then within to given result

special: "view" withing fitting Argument, "arch-spec" as USP, "units" as ASP
    "unit" is also attribute

other: logic lambda


lib-items: library (version), from (get |->), spec, view, arch, unit,
   refinement end

joint keywords: free type, generated type, arch spec, unit spec,
   behaviourally refined

then followed by cons, mono, def, implies

-}
