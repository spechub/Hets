module Haskell.Hatchet.Pretty (
        Doc,            -- Abstract
        Mode(..), TextDetails(..),

        empty, nest,

        text, char, ptext,
        int, integer, float, double, rational,
        parens, brackets, braces, quotes, doubleQuotes,
        semi, comma, colon, space, equals,
        lparen, rparen, lbrack, rbrack, lbrace, rbrace,

        (<>), (<+>), hcat, hsep, 
        ($$), ($+$), vcat, 
        sep, cat, 
        fsep, fcat, 

        hang, punctuate,
        
        renderStyle, 
        render, fullRender
  ) where



infixl 6 <> 
infixl 6 <+>
infixl 5 $$, $+$






















empty                     :: Doc
text                      :: String -> Doc 
char                      :: Char -> Doc

semi, comma, colon, space, equals              :: Doc
lparen, rparen, lbrack, rbrack, lbrace, rbrace :: Doc

parens, brackets, braces  :: Doc -> Doc 
quotes, doubleQuotes      :: Doc -> Doc

int      :: Int -> Doc
integer  :: Integer -> Doc
float    :: Float -> Doc
double   :: Double -> Doc
rational :: Rational -> Doc






(<>)   :: Doc -> Doc -> Doc     -- Beside
hcat   :: [Doc] -> Doc          -- List version of <>
(<+>)  :: Doc -> Doc -> Doc     -- Beside, separated by space
hsep   :: [Doc] -> Doc          -- List version of <+>

($$)   :: Doc -> Doc -> Doc     -- Above; if there is no
                                -- overlap it "dovetails" the two
vcat   :: [Doc] -> Doc          -- List version of $$

cat    :: [Doc] -> Doc          -- Either hcat or vcat
sep    :: [Doc] -> Doc          -- Either hsep or vcat
fcat   :: [Doc] -> Doc          -- ``Paragraph fill'' version of cat
fsep   :: [Doc] -> Doc          -- ``Paragraph fill'' version of sep

nest   :: Int -> Doc -> Doc     -- Nested





hang :: Doc -> Int -> Doc -> Doc
punctuate :: Doc -> [Doc] -> [Doc]      -- punctuate p [d1, ... dn] = [d1 <> p, d2 <> p, ... dn-1 <> p, dn]





instance Show Doc where
  showsPrec prec doc cont = showDoc doc cont

render     :: Doc -> String             -- Uses default style
fullRender :: Mode
           -> Int                       -- Line length
           -> Float                     -- Ribbons per line
           -> (TextDetails -> a -> a)   -- What to do with text
           -> a                         -- What to do at the end
           -> Doc
           -> a                         -- Result

renderStyle  :: Style -> Doc -> String
data Style = Style { lineLength     :: Int,     -- In chars
                     ribbonsPerLine :: Float,   -- Ratio of ribbon length to line length
                     mode :: Mode
             }
style :: Style          -- The default style
style = Style { lineLength = 100, ribbonsPerLine = 2.5, mode = PageMode }

data Mode = PageMode            -- Normal 
          | ZigZagMode          -- With zig-zag cuts
          | LeftMode            -- No indentation, infinitely long lines
          | OneLineMode         -- All on one line


























































































semi  = char ';'
colon = char ':'
comma = char ','
space = char ' '
equals = char '='
lparen = char '('
rparen = char ')'
lbrack = char '['
rbrack = char ']'
lbrace = char '{'
rbrace = char '}'

int      n = text (show n)
integer  n = text (show n)
float    n = text (show n)
double   n = text (show n)
rational n = text (show n)
-- SIGBJORN wrote instead:
-- rational n = text (show (fromRationalX n))

quotes p        = char '`' <> p <> char '\''
doubleQuotes p  = char '"' <> p <> char '"'
parens p        = char '(' <> p <> char ')'
brackets p      = char '[' <> p <> char ']'
braces p        = char '{' <> p <> char '}'


hcat = foldr (<>)  empty
hsep = foldr (<+>) empty
vcat = foldr ($$)  empty

hang d1 n d2 = d1 $$ (nest n d2)

punctuate p []     = []
punctuate p (d:ds) = go d ds
                   where
                     go d [] = [d]
                     go d (e:es) = (d <> p) : go e es












data Doc
 = Empty                                -- empty
 | NilAbove Doc                         -- text "" $$ x
 | TextBeside TextDetails Int Doc       -- text s <> x  
 | Nest Int Doc                         -- nest k x
 | Union Doc Doc                        -- ul `union` ur
 | NoDoc                                -- The empty set of documents
 | Beside Doc Bool Doc                  -- True <=> space between
 | Above  Doc Bool Doc                  -- True <=> never overlap

type RDoc = Doc         -- RDoc is a "reduced Doc", guaranteed not to have a top-level Above or Beside


reduceDoc :: Doc -> RDoc
reduceDoc (Beside p g q) = beside p g (reduceDoc q)
reduceDoc (Above  p g q) = above  p g (reduceDoc q)
reduceDoc p              = p


data TextDetails = Chr  Char
                 | Str  String
                 | PStr String
space_text = Chr ' '
nl_text    = Chr '\n'



































        -- Arg of a NilAbove is always an RDoc
nilAbove_ p = NilAbove p

        -- Arg of a TextBeside is always an RDoc
textBeside_ s sl p = TextBeside s sl p

        -- Arg of Nest is always an RDoc
nest_ k p = Nest k p

        -- Args of union are always RDocs
union_ p q = Union p q



















empty = Empty

char  c = textBeside_ (Chr c) 1 Empty
text  s = case length   s of {sl -> textBeside_ (Str s)  sl Empty}
ptext s = case length s of {sl -> textBeside_ (PStr s) sl Empty}

nest k  p = mkNest k (reduceDoc p)        -- Externally callable version

-- mkNest checks for Nest's invariant that it doesn't have an Empty inside it
mkNest k       (Nest k1 p) = mkNest (k + k1) p
mkNest k       NoDoc       = NoDoc
mkNest k       Empty       = Empty
mkNest 0       p           = p                  -- Worth a try!
mkNest k       p           = nest_ k p

-- mkUnion checks for an empty document
mkUnion Empty q = Empty
mkUnion p q     = p `union_` q










p $$  q = Above p False q
p $+$ q = Above p True q

above :: Doc -> Bool -> RDoc -> RDoc
above (Above p g1 q1)  g2 q2 = above p g1 (above q1 g2 q2)
above p@(Beside _ _ _) g  q  = aboveNest (reduceDoc p) g 0 (reduceDoc q)
above p g q                  = aboveNest p             g 0 (reduceDoc q)

aboveNest :: RDoc -> Bool -> Int -> RDoc -> RDoc
-- Specfication: aboveNest p g k q = p $g$ (nest k q)

aboveNest NoDoc               g k q = NoDoc
aboveNest (p1 `Union` p2)     g k q = aboveNest p1 g k q `union_` 
                                      aboveNest p2 g k q
                                
aboveNest Empty               g k q = mkNest k q
aboveNest (Nest k1 p)         g k q = nest_ k1 (aboveNest p g (k - k1) q)
                                  -- p can't be Empty, so no need for mkNest
                                
aboveNest (NilAbove p)        g k q = nilAbove_ (aboveNest p g k q)
aboveNest (TextBeside s sl p) g k q = textBeside_ s sl rest
                                    where
                                      k1   = k - sl
                                      rest = case p of
                                                Empty -> nilAboveNest g k1 q
                                                other -> aboveNest  p g k1 q
aboveNest (Above _ _ _)       _ _ _ = impossibleRD
aboveNest (Beside _ _ _)      _ _ _ = impossibleRD

impossibleRD :: a
impossibleRD = error "The impossible happened (no reduceDoc?)"



nilAboveNest :: Bool -> Int -> RDoc -> RDoc
-- Specification: text s <> nilaboveNest g k q 
--              = text s <> (text "" $g$ nest k q)

nilAboveNest g k Empty       = Empty    -- Here's why the "text s <>" is in the spec!
nilAboveNest g k (Nest k1 q) = nilAboveNest g (k + k1) q

nilAboveNest g k q           | (not g) && (k > 0)        -- No newline if no overlap
                             = textBeside_ (Str (spaces k)) k q
                             | otherwise                        -- Put them really above
                             = nilAbove_ (mkNest k q)










p <>  q = Beside p False q
p <+> q = Beside p True  q

beside :: Doc -> Bool -> RDoc -> RDoc
-- Specification: beside g p q = p <g> q
 
beside NoDoc               g q   = NoDoc
beside (p1 `Union` p2)     g q   = (beside p1 g q) `union_` (beside p2 g q)
beside Empty               g q   = q
beside (Nest k p)          g q   = nest_ k (beside p g q)       -- p non-empty
beside p@(Beside p1 g1 q1) g2 q2 
           {- (A `op1` B) `op2` C == A `op1` (B `op2` C)  iff op1 == op2 
                                                 [ && (op1 == <> || op1 == <+>) ] -}
         | g1 == g2              = beside p1 g1 (beside q1 g2 q2)
         | otherwise             = beside (reduceDoc p) g2 q2
beside p@(Above _ _ _)     g q   = beside (reduceDoc p) g q
beside (NilAbove p)        g q   = nilAbove_ (beside p g q)
beside (TextBeside s sl p) g q   = textBeside_ s sl rest
                               where
                                  rest = case p of
                                           Empty -> nilBeside g q
                                           other -> beside p g q



nilBeside :: Bool -> RDoc -> RDoc
-- Specification: text "" <> nilBeside g p 
--              = text "" <g> p

nilBeside g Empty      = Empty  -- Hence the text "" in the spec
nilBeside g (Nest _ p) = nilBeside g p
nilBeside g p          | g         = textBeside_ space_text 1 p
                       | otherwise = p









-- Specification: sep ps  = oneLiner (hsep ps)
--                         `union`
--                          vcat ps

sep = sepX True         -- Separate with spaces
cat = sepX False        -- Don't

sepX x []     = empty
sepX x (p:ps) = sep1 x (reduceDoc p) 0 ps


-- Specification: sep1 g k ys = sep (x : map (nest k) ys)
--                            = oneLiner (x <g> nest k (hsep ys))
--                              `union` x $$ nest k (vcat ys)

sep1 :: Bool -> RDoc -> Int -> [Doc] -> RDoc
sep1 g NoDoc               k ys = NoDoc
sep1 g (p `Union` q)       k ys = sep1 g p k ys
                                  `union_`
                                  (aboveNest q False k (reduceDoc (vcat ys)))

sep1 g Empty               k ys = mkNest k (sepX g ys)
sep1 g (Nest n p)          k ys = nest_ n (sep1 g p (k - n) ys)

sep1 g (NilAbove p)        k ys = nilAbove_ (aboveNest p False k (reduceDoc (vcat ys)))
sep1 g (TextBeside s sl p) k ys = textBeside_ s sl (sepNB g p (k - sl) ys)
sep1 _ (Above _ _ _)       _ _  = impossibleRD
sep1 _ (Beside _ _ _)      _ _  = impossibleRD

-- Specification: sepNB p k ys = sep1 (text "" <> p) k ys
-- Called when we have already found some text in the first item
-- We have to eat up nests

sepNB g (Nest _ p)  k ys  = sepNB g p k ys

sepNB g Empty k ys        = oneLiner (nilBeside g (reduceDoc rest))
                                `mkUnion` 
                            nilAboveNest False k (reduceDoc (vcat ys))
                          where
                            rest | g         = hsep ys
                                 | otherwise = hcat ys

sepNB g p k ys            = sep1 g p k ys









fsep = fill True
fcat = fill False

-- Specification: 
--   fill []  = empty
--   fill [p] = p
--   fill (p1:p2:ps) = oneLiner p1 <#> nest (length p1) 
--                                          (fill (oneLiner p2 : ps))
--                     `union`
--                      p1 $$ fill ps

fill g []     = empty
fill g (p:ps) = fill1 g (reduceDoc p) 0 ps


fill1 :: Bool -> RDoc -> Int -> [Doc] -> Doc
fill1 g NoDoc               k ys = NoDoc
fill1 g (p `Union` q)       k ys = fill1 g p k ys
                                   `union_`
                                   (aboveNest q False k (fill g ys))

fill1 g Empty               k ys = mkNest k (fill g ys)
fill1 g (Nest n p)          k ys = nest_ n (fill1 g p (k - n) ys)

fill1 g (NilAbove p)        k ys = nilAbove_ (aboveNest p False k (fill g ys))
fill1 g (TextBeside s sl p) k ys = textBeside_ s sl (fillNB g p (k - sl) ys)
fill1 _ (Above _ _ _)       _ _  = impossibleRD
fill1 _ (Beside _ _ _)      _ _  = impossibleRD

fillNB g (Nest _ p)  k ys  = fillNB g p k ys
fillNB g Empty k []        = Empty
fillNB g Empty k (y:ys)    = nilBeside g (fill1 g (oneLiner (reduceDoc y)) k1 ys)
                             `mkUnion` 
                             nilAboveNest False k (fill g (y:ys))
                           where
                             k1 | g         = k - 1
                                | otherwise = k

fillNB g p k ys            = fill1 g p k ys










best :: Mode
     -> Int             -- Line length
     -> Int             -- Ribbon length
     -> RDoc
     -> RDoc            -- No unions in here!

best OneLineMode w r p
  = get p
  where
    get Empty               = Empty
    get NoDoc               = NoDoc
    get (NilAbove p)        = nilAbove_ (get p)
    get (TextBeside s sl p) = textBeside_ s sl (get p)
    get (Nest k p)          = get p             -- Elide nest
    get (p `Union` q)       = first (get p) (get q)
    get (Above _ _ _)       = impossibleRD
    get (Beside _ _ _)      = impossibleRD

best mode w r p
  = get w p
  where
    get :: Int          -- (Remaining) width of line
        -> Doc -> Doc
    get w Empty               = Empty
    get w NoDoc               = NoDoc
    get w (NilAbove p)        = nilAbove_ (get w p)
    get w (TextBeside s sl p) = textBeside_ s sl (get1 w sl p)
    get w (Nest k p)          = nest_ k (get (w - k) p)
    get w (p `Union` q)       = nicest w r (get w p) (get w q)
    get _ (Above _ _ _)       = impossibleRD
    get _ (Beside _ _ _)      = impossibleRD

    get1 :: Int         -- (Remaining) width of line
         -> Int         -- Amount of first line already eaten up
         -> Doc         -- This is an argument to TextBeside => eat Nests
         -> Doc         -- No unions in here!

    get1 w sl Empty               = Empty
    get1 w sl NoDoc               = NoDoc
    get1 w sl (NilAbove p)        = nilAbove_ (get (w - sl) p)
    get1 w sl (TextBeside t tl p) = textBeside_ t tl (get1 w (sl + tl) p)
    get1 w sl (Nest k p)          = get1 w sl p
    get1 w sl (p `Union` q)       = nicest1 w r sl (get1 w sl p) 
                                                   (get1 w sl q)
    get1 _ _  (Above _ _ _)       = impossibleRD
    get1 _ _  (Beside _ _ _)      = impossibleRD

nicest w r p q = nicest1 w r 0 p q
nicest1 w r sl p q | fits ((w `minn` r) - sl) p = p
                   | otherwise                   = q

fits :: Int     -- Space available
     -> Doc
     -> Bool    -- True if *first line* of Doc fits in space available
 
fits n p    | n < 0 = False
fits n NoDoc               = False
fits n Empty               = True
fits n (NilAbove _)        = True
fits n (TextBeside _ sl p) = fits (n - sl) p

minn x y | x < y    = x
         | otherwise = y






first p q | nonEmptySet p = p 
          | otherwise     = q

nonEmptySet NoDoc           = False
nonEmptySet (p `Union` q)      = True
nonEmptySet Empty              = True
nonEmptySet (NilAbove p)       = True           -- NoDoc always in first line
nonEmptySet (TextBeside _ _ p) = nonEmptySet p
nonEmptySet (Nest _ p)         = nonEmptySet p
nonEmptySet (Above _ _ _)      = impossibleRD
nonEmptySet (Beside _ _ _)     = impossibleRD





oneLiner :: Doc -> Doc
oneLiner NoDoc               = NoDoc
oneLiner Empty               = Empty
oneLiner (NilAbove p)        = NoDoc
oneLiner (TextBeside s sl p) = textBeside_ s sl (oneLiner p)
oneLiner (Nest k p)          = nest_ k (oneLiner p)
oneLiner (p `Union` q)       = oneLiner p
oneLiner (Above _ _ _)       = impossibleRD
oneLiner (Beside _ _ _)      = impossibleRD













-- renderStyle Style{mode, lineLength, ribbonsPerLine} doc 
renderStyle (Style ll rPL m) doc 
--  = fullRender mode lineLength ribbonsPerLine string_txt "" doc
  = fullRender m ll rPL string_txt "" doc

render doc       = showDoc doc ""
showDoc doc rest = fullRender PageMode 100 1.5 string_txt rest doc

string_txt (Chr c)   s  = c:s
string_txt (Str s1)  s2 = s1 ++ s2
string_txt (PStr s1) s2 = s1 ++ s2




fullRender OneLineMode _ _ txt end doc = easy_display space_text txt end (reduceDoc doc)
fullRender LeftMode    _ _ txt end doc = easy_display nl_text    txt end (reduceDoc doc)

fullRender mode line_length ribbons_per_line txt end doc
  = display mode line_length ribbon_length txt end best_doc
  where 
    best_doc = best mode hacked_line_length ribbon_length (reduceDoc doc)

    hacked_line_length, ribbon_length :: Int
    ribbon_length = round (fromIntegral line_length / ribbons_per_line)
    hacked_line_length = case mode of { ZigZagMode -> maxBound; other -> line_length }

display mode page_width ribbon_width txt end doc
  = case page_width - ribbon_width of { gap_width ->
    case gap_width `quot` 2 of { shift ->
    let
        lay k (Nest k1 p)  = lay (k + k1) p
        lay k Empty        = end
    
        lay k (NilAbove p) = nl_text `txt` lay k p
    
        lay k (TextBeside s sl p)
            = case mode of
                    ZigZagMode |  k >= gap_width
                               -> nl_text `txt` (
                                  Str (multi_ch shift '/') `txt` (
                                  nl_text `txt` (
                                  lay1 (k - shift) s sl p)))

                               |  k < 0
                               -> nl_text `txt` (
                                  Str (multi_ch shift '\\') `txt` (
                                  nl_text `txt` (
                                  lay1 (k + shift) s sl p )))

                    other -> lay1 k s sl p
    
        lay1 k s sl p = Str (indent k) `txt` (s `txt` lay2 (k + sl) p)
    
        lay2 k (NilAbove p)        = nl_text `txt` lay k p
        lay2 k (TextBeside s sl p) = s `txt` (lay2 (k + sl) p)
        lay2 k (Nest _ p)          = lay2 k p
        lay2 k Empty               = end
    in
    lay 0 doc
    }}

cant_fail = error "easy_display: NoDoc"
easy_display nl_text txt end doc 
  = lay doc cant_fail
  where
    lay NoDoc               no_doc = no_doc
    lay (Union p q)         no_doc = {- lay p -} (lay q cant_fail)              -- Second arg can't be NoDoc
    lay (Nest k p)          no_doc = lay p no_doc
    lay Empty               no_doc = end
    lay (NilAbove p)        no_doc = nl_text `txt` lay p cant_fail      -- NoDoc always on first line
    lay (TextBeside s sl p) no_doc = s `txt` lay p no_doc

indent n | n >= 8 = '\t' : indent (n - 8)
         | otherwise      = spaces n

multi_ch 0 ch = ""
multi_ch n       ch = ch : multi_ch (n - 1) ch

spaces 0 = ""
spaces n       = ' ' : spaces (n - 1)


