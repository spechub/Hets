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
    , funArrow
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
import Common.Keywords
import Common.AS_Annotation
import Common.GlobalAnnotations
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Pretty as Pretty
import Common.LaTeX_funs
import Data.Char

infixl 6 <>
infixl 6 <+>
infixl 5 $+$

data TextKind =
    IdKind | Symbol | Comment | Keyword | TopKey | Indexed | StructId
    | Native

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
colon = text colonS

-- the only legal white space within Text
space :: Doc                 -- ^ A horizontal space (omitted at end of line)
space = text " "

equals :: Doc                 -- ^ A '=' character
equals = text equalS

-- use symbol for signs that need to be put in mathmode for latex
symbol :: String -> Doc
symbol = Text Symbol


-- for text within comments
commentText :: String -> Doc
commentText = Text Comment


-- don't escape this strings since they are interpreted by latex
native :: String -> Doc
native = Text Native

lparen, rparen, lbrack, rbrack, lbrace, rbrace, quote, doubleQuote :: Doc

lparen = symbol "("
rparen = symbol ")"
lbrack = symbol "["
rbrack = symbol "]"
lbrace = symbol "{"  -- to allow for latex translations
rbrace = symbol "}"
quote = symbol "\'"
doubleQuote = symbol "\""

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
dot, bullet, defn, less, lambda, mapsto, funArrow, pfun, cfun, pcfun,
   exequal, forallDoc, exists, unique, cross, bar, notDoc, inDoc, andDoc,
   orDoc, implies, equiv :: Doc

dot = text dotS
bullet = symbol dotS
defn = symbol defnS
less = symbol lessS
lambda = symbol lambdaS
mapsto = symbol mapsTo
funArrow = symbol funS
pfun = symbol pFun
cfun = symbol contFun
pcfun = symbol pContFun
exequal = symbol exEqual
forallDoc = symbol forallS
exists = symbol existsS
unique = symbol existsUnique
cross = symbol prodS
bar = symbol barS
notDoc = symbol notS
inDoc = symbol inS
andDoc = symbol lAnd
orDoc = symbol lOr
implies = symbol implS
equiv = symbol equivS

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

-- * folding stuff

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

anyRecord :: DocRecord a
anyRecord = DocRecord
    { foldEmpty = error "anyRecord.Empty"
    , foldAnnoDoc = error "anyRecord.AnnoDoc"
    , foldIdDoc = error "anyRecord.IdDoc"
    , foldIdApplDoc = error "anyRecord.IdApplDoc"
    , foldText = error "anyRecord.Text"
    , foldCat = error "anyRecord.Cat"
    , foldAttr = error "anyRecord.Attr"
    , foldIndentBy = error "anyRecord.IndentBy"
    }

-- * conversions

-- | simple conversion to a standard text document
toText :: Doc -> Pretty.Doc
toText = foldDoc anyRecord
    { foldEmpty = \ _ -> Pretty.empty
    , foldText = \ _ _ -> Pretty.text
    , foldCat = \ _ c -> case c of
          Vert -> Pretty.vcat
          Horiz -> Pretty.hcat
          HorizOrVert -> Pretty.cat
          Fill -> Pretty.fcat
    , foldAttr = \ _ _ -> id
    , foldIndentBy = \ _ d1 d2 d3 ->
          d2 Pretty.$$ Pretty.nest (length $ show d1) d3
    } . codeOut emptyGlobalAnnos Nothing Map.empty

-- | conversion to latex
toLatex :: GlobalAnnos -> Doc -> Pretty.Doc
toLatex ga = let dm = Map.map (Map.! DF_LATEX) .
                      Map.filter (Map.member DF_LATEX) $ display_annos ga
    in foldDoc anyRecord
    { foldEmpty = \ _ -> Pretty.empty
    , foldText = \ _ k s -> textToLatex False k s
    , foldCat = \ _ c l -> case c of
        Horiz -> Pretty.hcat l
        _ -> latex_macro setTab Pretty.<>
             latex_macro startTab Pretty.<> (case c of
          Vert -> Pretty.vcat
          Horiz -> error "toLatex.Horiz"
          HorizOrVert -> Pretty.cat
          Fill -> Pretty.fcat) l Pretty.<> latex_macro endTab
    , foldAttr = \ o k d -> case k of
          FlushRight -> flushright d
          Small -> case o of
              Attr Small (Text j s) -> textToLatex True j s
              _ -> error "toLatex.Small"
    , foldIndentBy = \ _ d1 d2 d3 ->
          d2 Pretty.$$ Pretty.nest (length $ show d1) d3
    } . makeSmall False . codeOut ga (Just DF_LATEX) dm

textToLatex :: Bool -> TextKind -> String -> Pretty.Doc
textToLatex b k s = let e = escape_comment_latex s in
        if elem s $ map (: []) ",;[]() "
        then makeSmallLatex b $ casl_normal_latex s
        else case k of
    IdKind -> makeSmallLatex b $ hc_sty_id e
    Symbol -> makeSmallLatex b $ symbolToLatex s
    Comment -> (if b then makeSmallLatex b . casl_comment_latex
               else casl_normal_latex) e
               -- multiple spaces should be replaced by \hspace
    Keyword -> (if b then makeSmallLatex b . hc_sty_small_keyword
                else hc_sty_plain_keyword) e
    TopKey -> hc_sty_casl_keyword e
    Indexed -> hc_sty_structid_indexed e
    StructId -> hc_sty_structid e
    Native -> makeSmallLatex b $ hc_sty_axiom s

makeSmallLatex :: Bool -> Pretty.Doc -> Pretty.Doc
makeSmallLatex b d =
   if b then Pretty.hcat [latex_macro startAnno, d, latex_macro endAnno]
   else d

symbolToLatex :: String -> Pretty.Doc
symbolToLatex s = Map.findWithDefault (hc_sty_axiom
                                       $ escape_latex s) s latexSymbols

latexSymbols :: Map.Map String Pretty.Doc
latexSymbols = Map.fromList
    [ (dotS, bullet_latex)
    , (percentS, hc_sty_small_keyword "\\%")
    , (percents, hc_sty_small_keyword "\\%\\%")
    , ("{", casl_normal_latex "\\{")
    , ("}", casl_normal_latex "\\}")
    , ("__", hc_sty_axiom "\\_\\_")
    , (lambdaS, hc_sty_axiom "\\lambda")
    , (mapsTo, mapsto_latex)
    , (funS, rightArrow)
    , (contFun, cfun_latex)
    , (pContFun, pcfun_latex)
    , (exEqual, exequal_latex)
    , (forallS, forall_latex)
    , (existsS, exists_latex)
    , (existsUnique, unique_latex)
    , (prodS, hc_sty_axiom "\\times")
    , (notS, hc_sty_axiom "\\neg")
    , (inS, hc_sty_axiom "\\in")
    , (lAnd, hc_sty_axiom "\\wedge")
    , (lOr, hc_sty_axiom "\\vee")
    , (implS, hc_sty_axiom "\\Rightarrow")
    , (equivS, hc_sty_axiom "\\Leftrightarrow") ]

makeSmall :: Bool -> Doc -> Doc
makeSmall b = foldDoc idRecord
    { foldAttr = \ _ k d -> makeSmall (case k of
                       Small -> True
                       _ -> b) d
    , foldCat = \ (Cat c l) _ _ -> Cat c $ map (makeSmall b) l
    , foldIndentBy = \ (IndentBy d1 d2 d3) _ _ _ ->
          IndentBy (makeSmall b d1) (makeSmall b d2) $ makeSmall b d3
    , foldText = \ d _ _ -> if b then Attr Small d else d
    }

-- * coding out stuff

{- | transform document according to a specific display map and other
global annotations like precedences, associativities, and literal
annotations. -}
codeOut :: GlobalAnnos -> Maybe Display_format -> Map.Map Id [Token] -> Doc
        -> Doc
codeOut ga d m = foldDoc idRecord
    { foldAnnoDoc = \ _ -> small . codeOutAnno d m
    , foldIdDoc = \ _ -> codeOutId m
    , foldIdApplDoc = \ _ -> codeOutAppl ga m
    }

codeToken :: String -> Doc
codeToken s = case s of
    [] -> empty
    h : _ -> (if isAlphaNum h || elem h "._'" then text else symbol) s

codeOrigId :: Id -> [Doc]
codeOrigId = map (codeToken . tokStr) . getTokenList place

codeIdToks :: [Token] -> [Doc]
codeIdToks = map (\ t -> let s = tokStr t in
                         if isPlace t then symbol s else native s)

codeOutId :: Map.Map Id [Token] -> Id -> Doc
codeOutId m i = hcat $ case Map.lookup i m of
    Nothing -> codeOrigId i
    Just ts -> codeIdToks ts

-- print literal terms and mixfix applications
codeOutAppl :: GlobalAnnos -> Map.Map Id [Token] -> Id -> [Doc] -> Doc
codeOutAppl _ m i args = codeOutId m i <> parens (fsep $ punctuate comma args)

annoLine :: String -> Doc
annoLine w = percent <> keyword w

annoLparen :: String -> Doc
annoLparen w = percent <> keyword w <> lparen

wrapAnnoLines :: Maybe Display_format -> Doc -> [String] -> Doc -> Doc
wrapAnnoLines d a l b = case map (commentText .
          maybe id (const $ dropWhile isSpace) d) l of
    [] -> a <> b
    [x] -> hcat [a, x, b]
    ds@(x : r) -> case d of
        Nothing -> vcat $ fcat [a, x] : init r ++ [fcat [last r, b]]
        Just _ -> a <+> vcat ds <> b

percent :: Doc
percent = symbol percentS

annoRparen :: Doc
annoRparen = rparen <> percent

cCommaT :: Map.Map Id [Token] -> [Id] -> [Doc]
cCommaT m = punctuate comma . map (codeOutId m)

hCommaT :: Map.Map Id [Token] -> [Id] -> Doc
hCommaT m = hsep . cCommaT m

fCommaT :: Map.Map Id [Token] -> [Id] -> Doc
fCommaT m = fsep . cCommaT m

codeOutAnno :: Maybe Display_format -> Map.Map Id [Token] -> Annotation -> Doc
codeOutAnno d m a = case a of
    Unparsed_anno aw at _ -> case at of
        Line_anno s -> (case aw of
            Annote_word w -> annoLine w
            Comment_start -> symbol percents) <> commentText s
        Group_anno l -> case aw of
            Annote_word w -> wrapAnnoLines d (annoLparen w) l annoRparen
            Comment_start -> wrapAnnoLines d (percent <> lbrace) l
                             (rbrace <> percent)
    Display_anno i ds _ -> annoLparen displayS <> fsep
        ( hcat (codeOrigId i) :
          map ( \ (df, s) -> percent <> text (lookupDisplayFormat df)
                <+> maybe (commentText s) (const $ codeOutId m i)
                    (Map.lookup i m)) ds) <> annoRparen
    List_anno i1 i2 i3 _ -> annoLine listS <+> hCommaT m [i1, i2, i3]
    Number_anno i _ -> annoLine numberS <+> codeOutId m i
    Float_anno i1 i2 _ -> annoLine floatingS <+> hCommaT m [i1, i2]
    String_anno i1 i2 _ -> annoLine stringS <+> hCommaT m [i1, i2]
    Prec_anno p l1 l2 _ -> annoLparen precS <>
        fsep [ braces $ fCommaT m l1
             , symbol $ case p of
                          Lower -> lessS
                          Higher -> greaterS
                          BothDirections -> diamondS
                          NoDirection -> error "codeOutAnno"
             , braces $ fCommaT m l2
             ] <> annoRparen
    Assoc_anno s l _ -> annoLparen (case s of
                          ALeft -> left_assocS
                          ARight -> right_assocS)
                        <> fCommaT m l <> annoRparen
    Label l _ -> wrapAnnoLines d (annoLparen "") l annoRparen
    Semantic_anno sa _ -> annoLine $ lookupSemanticAnno sa
