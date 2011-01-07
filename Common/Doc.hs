{- |
Module      :  $Header$
Description :  document data type Doc for (pretty) printing in various formats
Copyright   :  (c) Christian Maeder and Uni Bremen 2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

This module contains a document data type 'Doc' for displaying
(heterogenous) CASL specifications at least as plain text and latex
(and maybe html as well)

Inspired by John Hughes's and Simon Peyton Jones's Pretty Printer
Combinators in Text.PrettyPrint.HughesPJ, Thomas Hallgren's
PrettyDoc within programatica,
Daan Leijen's PPrint: A prettier printer 2001, and Olaf Chiti's Pretty
printing with lazy Dequeues 2003

The main combinators are those of HughesPJ except
nest, hang and $$. Instead of $$ '$+$' must be used that always forces a
line break. Indentation must be constructed using '<>' or '<+>', i.e.
'text' \"spec\" '<+>' MultilineBlock.

Also char, ptext, int, integer, float, double and rational do not
exist. These can all be simulated using 'text' (and 'show'). There's
an instance for 'Int' in "Common.DocUtils".

Furthermore, documents can no longer be tested with isEmpty. 'empty'
documents are silently ignored (as by HughesPJ) and
often it is more natural (or even necessary anyway) to test the
original data structure for emptiness.

Putting a document into braces should be done using 'specBraces' (but
a function braces is also exported), ensuring that opening and closing
braces are in the same column if the whole document does not fit on a
single line.

Rendering of documents is achieved by translations to the old
"Common.Lib.Pretty". For plain text simply 'show' can be
used. Any document can be translated to LaTeX via 'toLatex' and then
processed further by "Common.PrintLaTeX". If you like the output is a
different question, but the result should be legal LaTeX in
conjunction with the hetcasl.sty file.

For nicer looking LaTeX the predefined symbol constants should be
used! There is a difference between 'bullet' and 'dot' that is not
visible in plain text.

There are also three kinds of keywords, a plain 'keyword', a
'topSigKey' having the width of \"preds\", and a 'topKey' having the
width of \"view\". In plain text only inserted spaces are visible.

Strings in small caps are created by 'structId' and
'indexed'. The latter puts the string also into a LaTeX index.

In order to avoid considering display annotations and precedences,
documents can be constructed using 'annoDoc', 'idDoc', and 'idApplDoc'.

Currently only a few annotations (i.e. labels and %implied) are
printed 'flushRight'. This function is problematic as it does not
prevent something to be appended using '<>' or '<+>'. Furthermore
flushed parts are currently only visible in plain text, if they don't
fit on the same line (as nest is used for indenting).

Further functions are documented in "Common.DocUtils".

Examples can be produced using: hets -v2 -o pp.het,pp.tex
-}

module Common.Doc
    ( -- * the document type
      Doc
    , renderHtml
      -- * primitive documents
    , empty
    , space
    , semi
    , comma
    , colon
    , quMarkD
    , equals
    , lparen
    , rparen
    , lbrack
    , rbrack
    , lbrace
    , rbrace
      -- * converting strings into documents
    , text
    , codeToken
    , commentText
    , keyword
    , topSigKey
    , topKey
    , indexed
    , structId
      -- * wrapping documents in delimiters
    , parens
    , brackets
    , braces
    , specBraces
    , quotes
    , doubleQuotes
      -- * combining documents
    , (<>)
    , (<+>)
    , hcat
    , hsep
    , ($+$)
    , ($++$)
    , vcat
    , vsep
    , sep
    , cat
    , fsep
    , fcat
    , punctuate
    , sepByCommas
    , sepBySemis
      -- * symbols possibly rendered differently for Text or LaTeX
    , dot
    , bullet
    , defn
    , less
    , greater
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
    , prefix_proc
    , sequential
    , interleave
    , synchronous
    , genpar_open
    , genpar_close
    , alpar_open
    , alpar_sep
    , alpar_close
    , external_choice
    , internal_choice
    , hiding_proc
    , ren_proc_open
    , ren_proc_close
    , dagger
    , vdash
    , dashv
    , breve
      -- * docifying annotations and ids
    , annoDoc
    , idDoc
    , idLabelDoc
    , predIdApplDoc
    , idApplDoc
      -- * transforming to existing formats
    , toText
    , toHtml
    , toLatex
      -- * manipulating documents
    , flushRight
    , changeGlobalAnnos
    , rmTopKey
    ) where

import Common.AS_Annotation
import Common.ConvertLiteral
import Common.GlobalAnnotations
import Common.Id
import Common.Keywords
import Common.LaTeX_funs
import Common.Prec
import qualified Common.Lib.Pretty as Pretty

import Data.Char
import Data.List
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set

infixl 6 <>
infixl 6 <+>
infixl 5 $+$
infixl 5 $++$

-- * the data type

data LabelKind = IdDecl | IdAppl deriving (Show, Eq)

data TextKind =
    IdKind | IdSymb | Symbol | Comment | Keyword | TopKey Int
           | Indexed | StructId | Native | HetsLabel
           | IdLabel LabelKind TextKind Id

data Format = Small | FlushRight

data ComposeKind
    = Vert   -- ($+$) (no support for $$!)
    | Horiz  -- (<>)
    | HorizOrVert -- either Horiz or Vert
    | Fill
      deriving Eq

-- | an abstract data type
data Doc
    = Empty          -- creates an empty line if composed vertically
    | AnnoDoc Annotation -- we know how to print annotations
    | IdDoc LabelKind Id -- for plain ids outside applications
    | IdApplDoc Bool Id [Doc] -- for mixfix applications and literal terms
    | Text TextKind String -- non-empty and no white spaces inside
    | Cat ComposeKind [Doc]
    | Attr Format Doc      -- for annotations
    | ChangeGlobalAnnos (GlobalAnnos -> GlobalAnnos) Doc

instance Show Doc where
    showsPrec _ doc cont =
        Pretty.renderStyle' cont Pretty.style $ toText emptyGlobalAnnos doc

renderHtml :: GlobalAnnos -> Doc -> String
renderHtml ga = replSpacesForHtml 0
  . Pretty.renderStyle' "" Pretty.style . toHtml ga

replSpacesForHtml :: Int -> String -> String
replSpacesForHtml n s = case s of
  "" -> ""
  c : r -> case c of
    '\n' -> c : "<br />" ++ replSpacesForHtml 0 r
    ' ' -> replSpacesForHtml (n + 1) r
    _ -> (case n of
      0 -> (c :)
      1 -> ([' ', c] ++)
      _ -> ((' ' : concat (replicate n "&nbsp; ") ++ [c]) ++))
      $ replSpacesForHtml 0 r

isEmpty :: Doc -> Bool
isEmpty d = case d of
              Empty -> True
              Cat _ [] -> True
              _ -> False

-- * the visible interface

empty :: Doc                 -- ^ An empty document
empty = Empty

text :: String -> Doc
text s = case lines s of
    [] -> Text IdKind ""
    [x] -> Text IdKind x
    l -> vcat $ map (Text IdKind) l

semi :: Doc                 -- ^ A ';' character
semi = text ";"

comma :: Doc                 -- ^ A ',' character
comma = text ","

colon :: Doc                 -- ^ A ':' character
colon = symbol colonS

-- the only legal white space within Text
space :: Doc                 -- ^ A horizontal space (omitted at end of line)
space = text " "

equals :: Doc                 -- ^ A '=' character
equals = symbol equalS

-- use symbol for signs that need to be put in mathmode for latex
symbol :: String -> Doc
symbol = Text Symbol

-- for text within comments
commentText :: String -> Doc
commentText = Text Comment

-- put this string into math mode for latex and don't escape it
native :: String -> Doc
native = Text Native

lparen, rparen, lbrack, rbrack, lbrace, rbrace, quote, doubleQuote :: Doc

lparen = text "("
rparen = text ")"
lbrack = text "["
rbrack = text "]"
lbrace = symbol "{"  -- to allow for latex translations
rbrace = symbol "}"
quote = symbol "\'"
doubleQuote = symbol "\""

parens :: Doc -> Doc     -- ^ Wrap document in @(...)@
parens d = hcat [lparen, d, rparen]

brackets :: Doc -> Doc     -- ^ Wrap document in @[...]@
brackets d = hcat [lbrack, d, rbrack]

braces :: Doc -> Doc     -- ^ Wrap document in @{...}@
braces d = hcat [lbrace, d, rbrace]

specBraces :: Doc -> Doc     -- ^ Wrap document in @{...}@
specBraces d = cat [addLBrace d, rbrace]

-- | move the opening brace inwards
addLBrace :: Doc -> Doc
addLBrace d = case d of
    Cat k (e : r) -> Cat k $ addLBrace e : r
    ChangeGlobalAnnos f e -> ChangeGlobalAnnos f $ addLBrace e
    _ -> lbrace <> d

quotes :: Doc -> Doc     -- ^ Wrap document in @\'...\'@
quotes d = hcat [quote, d, quote]

doubleQuotes :: Doc -> Doc     -- ^ Wrap document in @\"...\"@
doubleQuotes d = hcat [doubleQuote, d, doubleQuote]

(<>) :: Doc -> Doc -> Doc      -- ^Beside
a <> b = hcat [a, b]

rmEmpties :: [Doc] -> [Doc]
rmEmpties = filter (not . isEmpty)

hcat :: [Doc] -> Doc          -- ^List version of '<>'
hcat = Cat Horiz . rmEmpties

(<+>) :: Doc -> Doc -> Doc     -- ^Beside, separated by space
a <+> b = hsep [a, b]

punctuate :: Doc -> [Doc] -> [Doc]
punctuate d l = case l of
     x : r@(_ : _) -> (x <> d) : punctuate d r
     _ -> l

hsep :: [Doc] -> Doc         -- ^List version of '<+>'
hsep = Cat Horiz . punctuate space . rmEmpties

($+$) :: Doc -> Doc -> Doc    -- ^Above, without dovetailing.
a $+$ b = vcat [a, b]

-- | vertical composition with a specified number of blank lines
aboveWithNLs :: Int -> Doc -> Doc -> Doc
aboveWithNLs n d1 d2
  | isEmpty d2 = d1
  | isEmpty d1 = d2
  | otherwise = d1 $+$ foldr ($+$) d2 (replicate n $ text "")

-- | vertical composition with one blank line
($++$) :: Doc -> Doc -> Doc
($++$) = aboveWithNLs 1

-- | list version of '($++$)'
vsep :: [Doc] -> Doc
vsep = foldr ($++$) empty

vcat :: [Doc] -> Doc          -- ^List version of '$+$'
vcat = Cat Vert . rmEmpties

cat :: [Doc] -> Doc          -- ^ Either hcat or vcat
cat = Cat HorizOrVert . rmEmpties

sep :: [Doc] -> Doc          -- ^ Either hsep or vcat
sep = Cat HorizOrVert . punctuate space . rmEmpties

fcat :: [Doc] -> Doc          -- ^ \"Paragraph fill\" version of cat
fcat = Cat Fill . rmEmpties

fsep :: [Doc] -> Doc          -- ^ \"Paragraph fill\" version of sep
fsep = Cat Fill . punctuate space . rmEmpties

keyword, topSigKey, topKey, indexed, structId :: String -> Doc
keyword = Text Keyword
indexed = Text Indexed
structId = Text StructId
topKey = Text (TopKey 4)
topSigKey = Text (TopKey 5)

lambdaSymb, daggerS, vdashS, dashvS, breveS :: String
lambdaSymb = "\\"
daggerS = "!"
vdashS = "|-"
dashvS = "-|"
breveS = "~"

-- docs possibly rendered differently for Text or LaTeX
quMarkD, dot, bullet, defn, less, greater, lambda, mapsto, funArrow, pfun,
   cfun, pcfun, exequal, forallDoc, exists, unique, cross, bar, notDoc,
   inDoc, andDoc, orDoc, implies, equiv, prefix_proc, sequential,
   interleave, synchronous, genpar_open, genpar_close, alpar_open,
   alpar_sep, alpar_close, external_choice, internal_choice, hiding_proc,
   ren_proc_open, ren_proc_close, dagger, vdash, dashv, breve :: Doc

quMarkD = text quMark
dot = text dotS
bullet = symbol dotS
defn = symbol defnS
less = symbol lessS
greater = symbol greaterS
lambda = symbol lambdaSymb
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
prefix_proc = symbol prefix_procS
sequential = text sequentialS
interleave = symbol interleavingS
synchronous = symbol synchronousS
genpar_open = symbol genpar_openS
genpar_close = symbol genpar_closeS
alpar_open = symbol alpar_openS
-- note that alpar_sepS and synchronousS are equal
alpar_sep = symbol alpar_sepS
alpar_close = symbol alpar_closeS
external_choice = symbol external_choiceS
internal_choice = symbol internal_choiceS
hiding_proc = text hiding_procS -- otherwise it clashes with lambda
ren_proc_open = symbol ren_proc_openS
ren_proc_close = symbol ren_proc_closeS
dagger = symbol daggerS
vdash = symbol vdashS
dashv = symbol dashvS
breve = symbol breveS

-- | we know how to print annotations
annoDoc :: Annotation -> Doc
annoDoc = AnnoDoc

-- | for plain ids outside of terms
idDoc :: Id -> Doc
idDoc = IdDoc IdAppl

-- | for newly declared ids
idLabelDoc :: Id -> Doc
idLabelDoc = IdDoc IdDecl

-- | for mixfix applications and literal terms (may print \"\" for empty)
idApplDoc :: Id -> [Doc] -> Doc
idApplDoc = IdApplDoc False

-- | for mixfix applications of predicate identifiers
predIdApplDoc :: Id -> [Doc] -> Doc
predIdApplDoc = IdApplDoc True

-- | put document as far to the right as fits (for annotations)
flushRight :: Doc -> Doc
flushRight = Attr FlushRight

small :: Doc -> Doc
small = Attr Small

-- * folding stuff

data DocRecord a = DocRecord
    { foldEmpty :: Doc -> a
    , foldAnnoDoc :: Doc -> Annotation -> a
    , foldIdDoc :: Doc -> LabelKind -> Id -> a
    , foldIdApplDoc :: Doc -> Bool -> Id -> [a] -> a
    , foldText :: Doc -> TextKind -> String -> a
    , foldCat :: Doc -> ComposeKind -> [a] -> a
    , foldAttr :: Doc -> Format -> a -> a
    , foldChangeGlobalAnnos :: Doc -> (GlobalAnnos -> GlobalAnnos) -> a -> a
    }

foldDoc :: DocRecord a -> Doc -> a
foldDoc r d = case d of
    Empty -> foldEmpty r d
    AnnoDoc a -> foldAnnoDoc r d a
    IdDoc l i -> foldIdDoc r d l i
    IdApplDoc b i l -> foldIdApplDoc r d b i $ map (foldDoc r) l
    Text k s -> foldText r d k s
    Cat k l -> foldCat r d k $ map (foldDoc r) l
    Attr a e -> foldAttr r d a $ foldDoc r e
    ChangeGlobalAnnos f e -> foldChangeGlobalAnnos r d f $ foldDoc r e

idRecord :: DocRecord Doc
idRecord = DocRecord
    { foldEmpty = const Empty
    , foldAnnoDoc = const AnnoDoc
    , foldIdDoc = const IdDoc
    , foldIdApplDoc = const IdApplDoc
    , foldText = const Text
    , foldCat = const Cat
    , foldAttr = const Attr
    , foldChangeGlobalAnnos = const ChangeGlobalAnnos
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
    , foldChangeGlobalAnnos = error "anyRecord.ChangeGlobalAnnos"
    }

-- * conversion to plain text

-- | simple conversion to a standard text document
toText :: GlobalAnnos -> Doc -> Pretty.Doc
toText ga = toTextAux . codeOut ga (mkPrecIntMap $ prec_annos ga)
            Nothing Map.empty

toTextAux :: Doc -> Pretty.Doc
toTextAux = foldDoc anyRecord
    { foldEmpty = const Pretty.empty
    , foldText = \ _ k s -> case k of
          TopKey n -> Pretty.text $ s ++ replicate (n - length s) ' '
          _ -> Pretty.text s
    , foldCat = \ d c l -> case d of
        Cat _ ds@(_ : _) -> if all hasSpace $ init ds then
          (case c of
          Vert -> Pretty.vcat
          Horiz -> Pretty.hsep
          HorizOrVert -> Pretty.sep
          Fill -> Pretty.fsep) $ map (toTextAux . rmSpace) ds
          else (case c of
          Vert -> Pretty.vcat
          Horiz -> Pretty.hcat
          HorizOrVert -> Pretty.cat
          Fill -> Pretty.fcat) l
        _ -> Pretty.empty
    , foldAttr = \ _ k d -> case k of
          FlushRight -> let l = length $ show d in
            if l < 66 then Pretty.nest (66 - l) d else d
          _ -> d
    , foldChangeGlobalAnnos = \ _ _ d -> d
    }

-- * conversion to html

-- | conversion to html
toHtml :: GlobalAnnos -> Doc -> Pretty.Doc
toHtml ga d = let
  dm = Map.map (Map.! DF_HTML)
       . Map.filter (Map.member DF_HTML) $ display_annos ga
  dis = getDeclIds d
  in foldDoc (toHtmlRecord dis) $ codeOut ga
                 (mkPrecIntMap $ prec_annos ga) (Just DF_HTML) dm d

toHtmlRecord :: Set.Set Id -> DocRecord Pretty.Doc
toHtmlRecord dis = anyRecord
    { foldEmpty = const Pretty.empty
    , foldText = const $ textToHtml dis
    , foldCat = \ d c l -> case d of
        Cat _ ds@(_ : _) -> if all hasSpace $ init ds then
          (case c of
          Vert -> Pretty.vcat
          Horiz -> Pretty.hsep
          HorizOrVert -> Pretty.sep
          Fill -> Pretty.fsep) $ map (foldDoc (toHtmlRecord dis) . rmSpace) ds
          else (case c of
          Vert -> Pretty.vcat
          Horiz -> Pretty.hcat
          HorizOrVert -> Pretty.cat
          Fill -> Pretty.fcat) l
        _ -> Pretty.empty
    , foldAttr = \ a k d -> case k of
          FlushRight ->
              let Attr _ o = a
                  l = length $ show $ toTextAux o
              in if l < 66 then Pretty.nest (66 - l) d else d
          _ -> d
    , foldChangeGlobalAnnos = \ _ _ d -> d
    }

textToHtml :: Set.Set Id -> TextKind -> String -> Pretty.Doc
textToHtml dis k s = let
  e = escapeHtml s ""
  h = Pretty.text e
  zeroText = Pretty.sp_text 0
  tagB t = '<' : t ++ ">"
  tagE t = tagB $ '/' : t
  tag t d = Pretty.hcat [zeroText (tagB t), d, zeroText (tagE t) ]
  tagBold = tag "strong"
  hi = tag "em" h
 in case k of
    Native -> Pretty.text s
    Keyword -> tagBold h
    TopKey n -> let l = n - length s in
      tagBold $ h Pretty.<> Pretty.text (replicate l ' ')
    Comment -> tag "small" h
    Indexed -> hi
    StructId -> hi
    HetsLabel -> tag "small" hi
    IdLabel appl tk i -> let
        d = textToHtml dis tk s
        si = escapeHtml (showId i "") ""
        in if not (Set.member i dis) then d else Pretty.hcat
        [zeroText $ "<a " ++ (if appl == IdAppl then "href=\"#" else "name=\"")
        ++ si ++ "\">", d, zeroText "</a>"]
    _ -> h

escChar :: Char -> ShowS
escChar c = case c of
  '\'' -> showString "&#39;"
  '<' -> showString "&lt;"
  '>' -> showString "&gt;"
  '&' -> showString "&amp;"
  '"' -> showString "&quot;"
  _ -> showChar c

escapeHtml :: String -> ShowS
escapeHtml cs rs = foldr escChar rs cs

-- * conversion to latex

toLatex :: GlobalAnnos -> Doc -> Pretty.Doc
toLatex ga d = let dm = Map.map (Map.! DF_LATEX) .
                      Map.filter (Map.member DF_LATEX) $ display_annos ga
                   dis = getDeclIds d
    in foldDoc (toLatexRecord dis False)
           . makeSmallMath False False $ codeOut ga
                 (mkPrecIntMap $ prec_annos ga) (Just DF_LATEX) dm d

-- avoid too many tabs
toLatexRecord :: Set.Set Id -> Bool -> DocRecord Pretty.Doc
toLatexRecord dis tab = anyRecord
    { foldEmpty = const Pretty.empty
    , foldText = const $ textToLatex dis False
    , foldCat = \ o _ _ -> case o of
        Cat c os@(d : r)
          | any isNative os -> Pretty.hcat $
             latex_macro "{\\Ax{"
             : map (foldDoc (toLatexRecord dis False)
                       { foldText = \ _ k s ->
                          case k of
                            Native -> Pretty.sp_text (axiom_width s) s
                            IdLabel _ Native _ ->
                                Pretty.sp_text (axiom_width s) s
                            IdKind | s == " " ->
                                Pretty.sp_text (axiom_width s) "\\,"
                            _ -> textToLatex dis False k s
                        }) os
              ++ [latex_macro "}}"]
          | null r -> foldDoc (toLatexRecord dis tab) d
          | otherwise -> (if tab && c /= Horiz then
                             (latex_macro setTab Pretty.<>)
                         . (latex_macro startTab Pretty.<>)
                         . (Pretty.<> latex_macro endTab)
                        else id)
                        $ (case c of
                             Vert -> Pretty.vcat
                             Horiz -> Pretty.hcat
                             HorizOrVert -> Pretty.cat
                             Fill -> Pretty.fcat)
                        $ case c of
                            Vert -> map (foldDoc $ toLatexRecord dis False) os
                            _ -> foldDoc (toLatexRecord dis False) d :
                                     map (foldDoc $ toLatexRecord dis True) r
        _ -> Pretty.empty
    , foldAttr = \ o k d -> case k of
          FlushRight -> flushright d
          Small -> case o of
              Attr Small (Text j s) -> textToLatex dis True j s
              _ -> makeSmallLatex True d
    , foldChangeGlobalAnnos = \ _ _ d -> d
    }

-- | move a small attribute inwards but not into mathmode bits
makeSmallMath :: Bool -> Bool -> Doc -> Doc
makeSmallMath smll math =
    foldDoc idRecord
    { foldAttr = \ o _ _ -> case o of
                       Attr Small d -> makeSmallMath True math d
                       Attr k d -> Attr k $ makeSmallMath smll math d
                       _ -> error "makeSmallMath.foldAttr"
    , foldCat = \ o _ _ -> case o of
                  Cat c l
                    | any isNative l ->
                        (if smll then Attr Small else id)
                        -- flatten math mode bits
                           $ Cat Horiz $ map
                                 (makeSmallMath False True . rmSpace) l
                    | math -> Cat Horiz
                         $ map (makeSmallMath False True) l
                    | smll && allHoriz o ->
                    -- produce fewer small blocks with wrong size though
                             Attr Small $ Cat Horiz $
                              map (makeSmallMath False math) l
                    | otherwise -> Cat c $ map (makeSmallMath smll math) l
                  _ -> error "makeSmallMath.foldCat"
    , foldText = \ d _ _ -> if smll then Attr Small d else d
    }

-- | check for unbalanced braces
needsMathMode :: Int -> String -> Bool
needsMathMode i s = case s of
    [] -> i > 0
    '{' : r -> needsMathMode (i + 1) r
    '}' : r -> i == 0 || needsMathMode (i - 1) r
    _ : r -> needsMathMode i r

isMathLatex :: Doc -> Bool
isMathLatex d = case d of
               Text Native s -> needsMathMode 0 s
               Text (IdLabel _ Native _) s -> needsMathMode 0 s
               Attr Small f -> isMathLatex f
               _ -> False

isNative :: Doc -> Bool
isNative d = case d of
               Cat Horiz [t, _] -> isMathLatex t
               _ -> isMathLatex d

-- | remove the spaces inserted by punctuate
rmSpace :: Doc -> Doc
rmSpace = snd . anaSpace

hasSpace :: Doc -> Bool
hasSpace = fst . anaSpace

anaSpace :: Doc -> (Bool, Doc)
anaSpace d = case d of
              Cat Horiz [t, Text IdKind s] | s == " " -> (True, t)
              _ -> (False, d)

allHoriz :: Doc -> Bool
allHoriz d = case d of
               Text _ _ -> True
               Cat Horiz l -> all allHoriz l
               Attr _ f -> allHoriz f
               Empty -> True
               _ -> False

makeSmallLatex :: Bool -> Pretty.Doc -> Pretty.Doc
makeSmallLatex b d = if b then
    Pretty.hcat [latex_macro startAnno, d, latex_macro endAnno] else d

symbolToLatex :: String -> Pretty.Doc
symbolToLatex s =
    Map.findWithDefault (hc_sty_axiom $ escapeLatex False s) s latexSymbols

getDeclIds :: Doc -> Set.Set Id
getDeclIds = foldDoc anyRecord
    { foldEmpty = const Set.empty
    , foldText = \ _ _ _ -> Set.empty
    , foldCat = \ _ _ -> Set.unions
    , foldAttr = \ _ _ d -> d
    , foldChangeGlobalAnnos = \ _ _ d -> d
    , foldIdDoc = \ _ lk i ->
          if lk == IdDecl then Set.singleton i else Set.empty
    , foldIdApplDoc = \ _ _ _ _ -> Set.empty
    , foldAnnoDoc = \ _ _ -> Set.empty
    }

textToLatex :: Set.Set Id -> Bool -> TextKind -> String -> Pretty.Doc
textToLatex dis b k s = case s of
  "" -> Pretty.text ""
  h : _ -> let e = escapeLatex True s in case k of
    IdKind -> makeSmallLatex b $ if elem s $ map (: []) ",;[]() "
              then casl_normal_latex s
              else hc_sty_id e
    IdSymb -> makeSmallLatex b $ if s == "__" then symbolToLatex s
              else if isAlpha h || elem h "._'" then hc_sty_id e
              else hc_sty_axiom $ escapeLatex False s
    Symbol -> makeSmallLatex b $ symbolToLatex s
    Comment -> makeSmallLatex b $ casl_comment_latex e
               -- multiple spaces should be replaced by \hspace
    Keyword -> (if b then makeSmallLatex b . hc_sty_small_keyword
                else hc_sty_plain_keyword) s
    TopKey _ -> hc_sty_casl_keyword s
    Indexed -> hc_sty_structid_indexed s
    StructId -> hc_sty_structid s
    Native -> hc_sty_axiom s
    HetsLabel -> Pretty.hcat [ latex_macro "\\HetsLabel{"
                             , textToLatex dis b Comment s
                             , latex_macro $ "}{" ++ escapeLabel s ++ "}" ]
    -- HetsLabel may be avoided by the Label case
    IdLabel appl tk i -> let d = textToLatex dis b tk s
                             si = showId i ""
        in if b || appl == IdAppl && not (Set.member i dis)
               || not (isLegalLabel si)
           -- make this case True to avoid labels
           then d else Pretty.hcat
            [ latex_macro $ '\\' : shows appl "Label{"
            , d
            , latex_macro $ "}{" ++ escapeLabel si ++ "}" ]

escapeLabel :: String -> String
escapeLabel = map ( \ c -> if c == '_' then ':' else c)

latexSymbols :: Map.Map String Pretty.Doc
latexSymbols = Map.union (Map.fromList
    [ ("{", casl_normal_latex "\\{")
    , ("}", casl_normal_latex "\\}")
    , (barS, casl_normal_latex "\\AltBar{}")
    , (percentS, hc_sty_small_keyword "\\%")
    , (percents, hc_sty_small_keyword "\\%\\%")
    , (exEqual, Pretty.sp_text (axiom_width "=") "\\Ax{\\stackrel{e}{=}}") ])
    $ Map.map hc_sty_axiom $ Map.fromList
    [ (dotS, "\\bullet")
    , (diamondS, "\\Diamond")
    , ("__", "\\_\\_")
    , (lambdaSymb, "\\lambda")
    , (mapsTo, "\\mapsto")
    , (funS, "\\rightarrow")
    , (pFun, "\\rightarrow?")
    , (contFun, "\\stackrel{c}{\\rightarrow}")
    , (pContFun, "\\stackrel{c}{\\rightarrow}?")
    , (forallS, "\\forall")
    , (existsS, "\\exists")
    , (existsUnique, "\\exists!")
    , (prodS, "\\times")
    , (notS, "\\neg")
    , (inS, "\\in")
    , (lAnd, "\\wedge")
    , (lOr, "\\vee")
    , (daggerS, "\\dag")
    , (vdashS, "\\vdash")
    , (dashvS, "\\dashv")
    , (breveS, "\\breve{~}")
    , (implS, "\\Rightarrow")
    , (equivS, "\\Leftrightarrow")
    , (prefix_procS, "\\rightarrow") -- clash with funS
    , (genpar_openS, "{|}\\mkern -2mu{[}\\mkern-1mu")
    , (genpar_closeS, "\\mkern-1mu{]}\\mkern -2mu{|}")
    , (alpar_openS, "{|}\\mkern -2mu{[}\\mkern-1mu")
    , (alpar_sepS, "\\cpar") -- overridden by synchronousS, below
    , (alpar_closeS, "\\mkern-1mu{]}\\mkern -2mu{|}")
    , (interleavingS, "{|}\\mkern-2mu{|}\\mkern-2mu{|}")
    , (synchronousS, "\\mid\\mid") -- must be after alpar_sepS (clash)
    , (external_choiceS, "\\Box")
    , (internal_choiceS, "\\sqcap")
    , (ren_proc_openS, "[")
    , (ren_proc_closeS, "]")
    ]

-- * coding out stuff

{- | transform document according to a specific display map and other
global annotations like precedences, associativities, and literal
annotations. -}
codeOut :: GlobalAnnos -> PrecMap -> Maybe Display_format
        -> Map.Map Id [Token] -> Doc -> Doc
codeOut ga precs d m = foldDoc idRecord
    { foldAnnoDoc = \ _ -> small . codeOutAnno m
    , foldIdDoc = \ _ lk -> codeOutId lk m
    , foldIdApplDoc = \ o _ _ -> codeOutAppl ga precs d m o
    , foldChangeGlobalAnnos = \ o _ _ ->
          let ChangeGlobalAnnos fg e = o
              ng = fg ga
          in codeOut ng (mkPrecIntMap $ prec_annos ng) d
             (maybe m (\ f -> Map.map (Map.! f) .
                      Map.filter (Map.member f) $ display_annos ng) d) e
    }

codeToken :: String -> Doc
codeToken = Text IdSymb

codeOrigId :: LabelKind -> Map.Map Id [Token] -> Id -> [Doc]
codeOrigId lk m i@(Id ts cs _) = let
    (toks, places) = splitMixToken ts
    conv = reverse . snd . foldl ( \ (b, l) t ->
           let s = tokStr t
           in if isPlace t then (b, symbol s : l)
              else (True, (if b then codeToken s else makeLabel lk IdSymb s i)
                            : l)) (False, [])
    in if null cs then conv ts
       else conv toks ++ codeCompIds m cs : conv places

cCommaT :: Map.Map Id [Token] -> [Id] -> [Doc]
cCommaT m = punctuate comma . map (codeOutId IdAppl m)

codeCompIds :: Map.Map Id [Token] -> [Id] -> Doc
codeCompIds m = brackets . fcat . cCommaT m

codeOutId :: LabelKind -> Map.Map Id [Token] -> Id -> Doc
codeOutId lk m i = fcat $ case Map.lookup i m of
    Nothing -> codeOrigId lk m i
    Just ts -> reverse $ snd $ foldl ( \ (b, l) t ->
        let s = tokStr t
        in if isPlace t then (b, symbol s : l) else
            (True, (if b then native s else
                        makeLabel lk Native s i) : l)) (False, []) ts

makeLabel :: LabelKind -> TextKind -> String -> Id -> Doc
makeLabel l k s i = Text (IdLabel l k i) s

annoLine :: String -> Doc
annoLine w = percent <> keyword w

annoLparen :: String -> Doc
annoLparen w = percent <> keyword w <> lparen

revDropSpaces :: String -> String
revDropSpaces = reverse . dropWhile isSpace

wrapLines :: TextKind -> Doc -> [String] -> Doc -> Doc
wrapLines k a l b = let p = (null (head l), null (last l)) in
  case map (Text k) l of
    [] -> a <> b
    [x] -> hcat [a, x, b]
    [x, y] -> case p of
        (True, c) -> a $+$ if c then b else y <> b
        (False, True) -> a <> x $+$ b
        _ -> a <> (x $+$ y <> b)
    x : r -> let
      m = init r
      y = last r
      xm = x : m
      am = a : m
      yb = [y <> b]
      in case p of
        (True, c) -> vcat $ am ++ if c then [b] else yb
        (False, True) -> a <> vcat xm $+$ b
        _ -> a <> vcat (xm ++ yb)

wrapAnnoLines :: Doc -> [String] -> Doc -> Doc
wrapAnnoLines = wrapLines Comment

percent :: Doc
percent = symbol percentS

annoRparen :: Doc
annoRparen = rparen <> percent

hCommaT :: Map.Map Id [Token] -> [Id] -> Doc
hCommaT m = hsep . cCommaT m

fCommaT :: Map.Map Id [Token] -> [Id] -> Doc
fCommaT m = fsep . cCommaT m

codeOutAnno :: Map.Map Id [Token] -> Annotation -> Doc
codeOutAnno m a = case a of
    Unparsed_anno aw at _ -> case at of
        Line_anno s -> (case aw of
            Annote_word w -> annoLine w
            Comment_start -> symbol percents)
                             <> commentText (revDropSpaces $ reverse s)
        Group_anno l -> case aw of
            Annote_word w -> wrapAnnoLines (annoLparen w) l annoRparen
            Comment_start -> wrapAnnoLines (percent <> lbrace) l
                             $ rbrace <> percent
    Display_anno i ds _ -> annoLparen displayS <> fsep
        ( fcat (codeOrigId IdAppl m i) :
          map ( \ (df, s) -> percent <> commentText (lookupDisplayFormat df)
                <+> maybe (commentText s) (const $ codeOutId IdAppl m i)
                    (Map.lookup i m)) ds) <> annoRparen
    List_anno i1 i2 i3 _ -> annoLine listS <+> hCommaT m [i1, i2, i3]
    Number_anno i _ -> annoLine numberS <+> codeOutId IdAppl m i
    Float_anno i1 i2 _ -> annoLine floatingS <+> hCommaT m [i1, i2]
    String_anno i1 i2 _ -> annoLine stringS <+> hCommaT m [i1, i2]
    Prec_anno p l1 l2 _ -> annoLparen precS <>
        fsep [ braces $ fCommaT m l1
             , case p of
                 Lower -> less
                 Higher -> greater
                 BothDirections -> less <> greater
                 NoDirection -> greater <> less
             , braces $ fCommaT m l2
             ] <> annoRparen
    Assoc_anno s l _ -> annoLparen (case s of
                          ALeft -> left_assocS
                          ARight -> right_assocS)
                        <> fCommaT m l <> annoRparen
    Label l _ -> wrapLines (case l of
                  [x] -> if isLegalLabel x
                         -- change this to False to avoid HetsLabel at all
                            then HetsLabel
                            else Comment
                  _ -> Comment) (percent <> lparen) l annoRparen
    Semantic_anno sa _ -> annoLine $ lookupSemanticAnno sa

isLegalLabel :: String -> Bool
isLegalLabel r = not (null r) && all ( \ c -> isAlphaNum c || elem c "_" ) r

splitDoc :: Doc -> Maybe (Id, [Doc])
splitDoc d = case d of
    IdApplDoc _ i l -> Just (i, l)
    _ -> Nothing

sepByCommas :: [Doc] -> Doc
sepByCommas = fsep . punctuate comma

sepBySemis :: [Doc] -> Doc
sepBySemis = fsep . punctuate semi

data Weight = Weight Int Id Id Id -- top, left, right

-- print literal terms and mixfix applications
codeOutAppl :: GlobalAnnos -> PrecMap -> Maybe Display_format
            -> Map.Map Id [Token] -> Doc -> [Doc] -> Doc
codeOutAppl ga precs md m origDoc args = case origDoc of
  IdApplDoc isPred i@(Id ts cs _) aas ->
    let mk = codeToken . tokStr
        pa = prec_annos ga
        assocs = assoc_annos ga
        mx = maxWeight precs
        pm = precMap precs
        e = Map.findWithDefault mx eqId pm
        p = Map.findWithDefault (if isInfix i then e else mx) i pm
        doSplit = fromMaybe (error "doSplit") . splitDoc
        mkList op largs cl = fsep $ codeOutId IdAppl m op : punctuate comma
                             (map (codeOut ga precs md m) largs)
                             ++ [codeOutId IdAppl m cl]
    in if isGenNumber splitDoc ga i aas then
             mk $ toNumber doSplit i aas
         else if isGenFrac splitDoc ga i aas then
             mk $ toFrac doSplit aas
         else if isGenFloat splitDoc ga i aas then
             mk $ toFloat doSplit ga aas
         else if isGenString splitDoc ga i aas then
             mk $ toString doSplit ga i aas
         else if isGenList splitDoc ga i aas then
             toMixfixList mkList doSplit ga i aas
         else if null args || length args /= placeCount i then
             codeOutId IdAppl m i <> if null args then empty else
                                  parens (sepByCommas args)
         else let
             parArgs = reverse $ foldl ( \ l (arg, dc) ->
                case getWeight ga precs arg of
                Nothing -> dc : l
                Just (Weight q ta la ra) ->
                    let pArg = parens dc
                        d = if isBoth pa i ta then pArg else dc
                        oArg = if (q < e || p >= e &&
                                         (notElem i [eqId, exEq]
                                         || elem ta [eqId, exEq]))
                                  && isDiffAssoc assocs pa i ta
                               then pArg else d
                    in (if isLeftArg i l then
                       if checkArg ARight ga (i, p) (ta, q) ra
                       then oArg
                       else if isPred || isSafeLhs i ta then d else pArg
                    else if isRightArg i l then
                       if checkArg ALeft ga (i, p) (ta, q) la
                       then oArg
                       else if (applId == i || isInfix ta)
                                && not isPred then pArg else d
                    else d) : l) [] $ zip aas args
             (fts, ncs, cFun) = case Map.lookup i m of
                            Nothing ->
                                (fst $ splitMixToken ts, cs, IdSymb)
                            Just nts -> (nts, [], Native)
             ((_, rArgs), fArgs) = mapAccumL ( \ (b, ac) t ->
               if isPlace t then case ac of
                 hd : tl -> ((b, tl), (False, hd))
                 _ -> error "Common.Doc.codeOutAppl1"
                 else ((True, ac), (True,
                       let s = tokStr t in
                       if b then Text cFun s else makeIdApplLabel cFun s i)))
                                                  (False, parArgs) fts
            in fsep $ hgroup $
               (if null ncs then fArgs
                else if null fArgs then error "Common.Doc.codeOutAppl2"
                     else init fArgs ++
                              [(True, snd (last fArgs) <> codeCompIds m cs)])
               ++ map ( \ d -> (False, d)) rArgs
  _ -> error "Common.Doc.codeOutAppl2"

hgroup :: [(Bool, Doc)] -> [Doc]
hgroup l = case l of
  (True, d1) : (False, d2) : r -> hsep [d1, d2] : hgroup r
  (_, d) : r -> d : hgroup r
  [] -> []

makeIdApplLabel :: TextKind -> String -> Id -> Doc
makeIdApplLabel k s i = Text (IdLabel IdAppl k i) s

getWeight :: GlobalAnnos -> PrecMap -> Doc -> Maybe Weight
getWeight ga precs d = let
    m = precMap precs
    in case d of
    IdApplDoc _ i aas@(hd : _) ->
        let p = Map.findWithDefault
              (if begPlace i || endPlace i then Map.findWithDefault 0 eqId m
               else maxWeight precs)
              i m in
        if isGenLiteral splitDoc ga i aas then Nothing else
        let lw = case getWeight ga precs hd of
                   Just (Weight _ _ l _) -> nextWeight ALeft ga i l
                   Nothing -> i
            rw = case getWeight ga precs $ last aas of
                   Just (Weight _ _ _ r) -> nextWeight ARight ga i r
                   Nothing -> i
            in Just $ Weight p i lw rw
    _ -> Nothing

{- checkArg allows any nested infixes that are not listed in the
   precedence graph in order to report ambiguities when parsed. The
   following case require parens when printed. -}
isDiffAssoc :: AssocMap -> PrecedenceGraph -> Id -> Id -> Bool
isDiffAssoc assocs precs op arg = isInfix op && isInfix arg &&
            if op /= arg then
               arg /= applId && case precRel precs op arg of
               Lower -> False
               _ -> True
            else not $ Map.member arg assocs

-- no need for parens in the following cases
isSafeLhs :: Id -> Id -> Bool
isSafeLhs op arg = applId /= op &&
    (applId == arg || isPostfix arg || endPlace op && not (isInfix arg))

isBoth :: PrecedenceGraph -> Id -> Id -> Bool
isBoth precs op arg = case precRel precs op arg of
                    BothDirections -> True
                    _ -> False

-- | change top-level to plain keywords
rmTopKey :: Doc -> Doc
rmTopKey = foldDoc idRecord
    { foldText = \ d k s -> case k of
          TopKey _ -> Text Keyword s
          _ -> d
    }

-- | add global annotations for proper mixfix printing
changeGlobalAnnos :: (GlobalAnnos -> GlobalAnnos) -> Doc -> Doc
changeGlobalAnnos = ChangeGlobalAnnos
