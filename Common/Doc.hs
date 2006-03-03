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
in "Text.PrettyPrint.HughesPJ", Thomas Hallgren's
<http://www.cse.ogi.edu/~hallgren/Programatica/tools/pfe.cgi?PrettyDoc>
Daan Leijen's PPrint: A prettier printer 2001, Olaf Chiti's
Pretty printing with lazy Dequeues 2003
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
    , flushRight
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
      -- * transforming to existing formats
    , codeOut
    , toText
    , toLatex
    ) where

import Common.Id
import Common.AS_Annotation
import Common.GlobalAnnotations
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Pretty as Pretty

infixl 6 <>
infixl 6 <+>
infixl 5 $+$

data TextKind = IdKind | Symbol | Keyword | TopKey | Indexed | StructId

data Format = Small | FlushRight

data ComposeKind
    = Vert   -- ($+$) (no support for $$!)
    | Horiz  -- (<>)
    | HorizOrVert -- either Horiz or Vert
    | Fill

data Doc
    = Empty          -- creates an empty line if composed vertically
    | AnnoDoc Annotation -- we know how to print annotations
    | IdDoc Id           -- for plain ids outside applications
    | IdApplDoc Id [Doc] -- for mixfix applications and literal terms
    | Text TextKind String -- non-empty and no white spaces inside
    | Cat ComposeKind [Doc]
    | Attr Format Doc      -- for annotations
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

-- the only legal white space within Text
space :: Doc                 -- ^ A horizontal space (omitted at end of line)
space = text " "

equals :: Doc                 -- ^ A '=' character
equals = text "="

-- use symbol for strings that need (i.e. latex) escaping
symbol :: String -> Doc
symbol = Text Symbol

lparen, rparen, lbrack, rbrack, lbrace, rbrace, quote, doubleQuote :: Doc

lparen = text "("
rparen = text ")"
lbrack = text "["
rbrack = text "]"
lbrace = symbol "{"  -- to allow for latex translations
rbrace = symbol "}"
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
bullet = symbol "."
defn = symbol "::="
less = text "<"
lambda = symbol "lambda"
mapsto = symbol "|->"
rightArrow = symbol "->"
pfun = symbol "->?"
cfun = symbol "-->"
pcfun = symbol "-->?"
exequal = symbol "=e="
forallDoc = symbol "forall"
exists = symbol "exists"
unique = symbol "exists!"
cross = symbol "*"
bar = symbol "|"
notDoc = symbol "not"
inDoc = symbol "in"
andDoc = symbol "/\\"
orDoc = symbol "\\/"
implies = symbol "=>"
equiv = symbol "<=>"

-- | we know how to print annotations
annoDoc :: Annotation -> Doc
annoDoc = AnnoDoc

-- | for plain ids outside applications
idDoc :: Id -> Doc
idDoc = IdDoc

-- | for mixfix applications and literal terms (may print \"\" for empty)
idApplDoc :: Id -> [Doc] -> Doc
idApplDoc = IdApplDoc

-- | put document as far to the right as fits (for annotations)
flushRight :: Doc -> Doc
flushRight = Attr FlushRight

small :: Doc -> Doc
small = Attr Small

{- | print second argument and then indent the last one by the width
of the first one -}
indentBy :: Doc -> Doc -> Doc -> Doc
indentBy = IndentBy

{- | transform document according to a specific display map and other
global annotations like precedences, associativities, and literal
annotations. -}
codeOut :: Map.Map Id [Token] -> GlobalAnnos -> Doc -> Doc
codeOut m _ = foldDoc idRecord { foldAnnoDoc = \ _ -> small . codeOutAnno m }

-- | convert for outputting latex
toLatex :: Doc -> Pretty.Doc
toLatex = undefined

-- | simple conversion to a standard text document
toText :: Doc -> Pretty.Doc
toText = undefined

data DocRecord a = DocRecord
    { foldEmpty :: Doc -> a
    , foldAnnoDoc :: Doc -> Annotation -> a
    , foldIdDoc :: Doc -> Id -> a
    , foldIdApplDoc :: Doc -> Id -> [a] -> a
    , foldText :: Doc -> TextKind -> String -> a
    , foldCat :: Doc -> ComposeKind -> [a] -> a
    , foldAttr :: Doc -> Format -> a -> a
    , foldIndentBy :: Doc -> a -> a -> a -> a
    }

idRecord :: DocRecord Doc
idRecord = DocRecord
    { foldEmpty = \ _ -> Empty
    , foldAnnoDoc = \ _ -> AnnoDoc
    , foldIdDoc = \ _ -> IdDoc
    , foldIdApplDoc = \ _ -> IdApplDoc
    , foldText = \ _ -> Text
    , foldCat = \ _ -> Cat
    , foldAttr = \ _ -> Attr
    , foldIndentBy = \ _ -> IndentBy
    }

foldDoc :: DocRecord a -> Doc -> a
foldDoc r d = case d of
    Empty -> foldEmpty r d
    AnnoDoc a -> foldAnnoDoc r d a
    IdDoc i -> foldIdDoc r d i
    IdApplDoc i l -> foldIdApplDoc r d i $ map (foldDoc r) l
    Text k s -> foldText r d k s
    Cat k l -> foldCat r d k $ map (foldDoc r) l
    Attr a e -> foldAttr r d a $ foldDoc r e
    IndentBy e f g ->
        foldIndentBy r d (foldDoc r e) (foldDoc r f) $ foldDoc r g

annoLine :: String -> Doc
annoLine w = symbol "%" <> text w

annoLparen :: String -> Doc
annoLparen w = symbol "%" <> text w <> lparen

wrapAnnoLines :: Doc -> [Doc] -> Doc -> Doc
wrapAnnoLines a l b = case l of
    [] -> a <> b
    [x] -> fcat [a, x, b]
    x : r -> vcat $ fcat [a, x] : init r ++ [fcat [last r, b]]

percent :: Doc
percent = symbol "%"

codeOutAnno :: Map.Map Id [Token] -> Annotation -> Doc
codeOutAnno m a = case a of
    Unparsed_anno aw at _ -> case at of
        Line_anno s -> (case aw of
            Annote_word w -> annoLine w
            Comment_start -> symbol "%%") <> symbol s
        Group_anno l -> let ds = map symbol l in case aw of
            Annote_word w -> wrapAnnoLines (annoLparen w) ds rparen
            Comment_start -> wrapAnnoLines (percent <> lbrace) ds rbrace
    Display_anno i ds _ -> annoLparen "display" <+> fsep
        [ codeOutId m i
        , vcat $ map ( \ (d, s) ->
                       percent <> text (lookupDisplayFormat d) <+> symbol s) ds
        , rparen ]
    _ -> error "codeOutAnno"

codeOutId :: Map.Map Id [Token] -> Id -> Doc
codeOutId m i = fcat $ case Map.lookup i m of
    Nothing -> map (symbol . tokStr) $ getTokenList place i
    Just ts -> map (\ t -> let s = tokStr t in
                           if isPlace t then symbol s else text s) ts
