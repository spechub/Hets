*********************************************************************************
*                                                                               *
*       John Hughes's and Simon Peyton Jones's Pretty Printer Combinators       *
*                                                                               *
*               based on "The Design of a Pretty-printing Library"              *
*               in Advanced Functional Programming,                             *
*               Johan Jeuring and Erik Meijer (eds), LNCS 925                   *
*               http://www.cs.chalmers.se/~rjmh/Papers/pretty.ps                *
*                                                                               *
*               Heavily modified by Simon Peyton Jones, Dec 96                  *
*                                                                               *
*********************************************************************************

Further Modifications done by Klaus L�ttich for rendering LaTeX in very 
special way.

Version 3.0     28 May 1997
  * Cured massive performance bug.  If you write

        foldl <> empty (map (text.show) [1..10000])

    you get quadratic behaviour with V2.0.  Why?  For just the same reason as you get
    quadratic behaviour with left-associated (++) chains.

    This is really bad news.  One thing a pretty-printer abstraction should
    certainly guarantee is insensivity to associativity.  It matters: suddenly
    GHC's compilation times went up by a factor of 100 when I switched to the
    new pretty printer.
 
    I fixed it with a bit of a hack (because I wanted to get GHC back on the
    road).  I added two new constructors to the Doc type, Above and Beside:
 
         <> = Beside
         $$ = Above
 
    Then, where I need to get to a "TextBeside" or "NilAbove" form I "force"
    the Doc to squeeze out these suspended calls to Beside and Above; but in so
    doing I re-associate. It's quite simple, but I'm not satisfied that I've done
    the best possible job.  I'll send you the code if you are interested.

  * Added new exports:
        punctuate, hang
        int, integer, float, double, rational,
        lparen, rparen, lbrack, rbrack, lbrace, rbrace,

  * fullRender's type signature has changed.  Rather than producing a string it
    now takes an extra couple of arguments that tells it how to glue fragments
    of output together:

        fullRender :: Mode
                   -> Int                       -- Line length
                   -> Float                     -- Ribbons per line
                   -> (TextDetails -> a -> a)   -- What to do with text
                   -> a                         -- What to do at the end
                   -> Doc
                   -> a                         -- Result

    The "fragments" are encapsulated in the TextDetails data type:
        data TextDetails = Chr  Char
                         | Str  String
                         | PStr FAST_STRING

    The Chr and Str constructors are obvious enough.  The PStr constructor has a packed
    string (FAST_STRING) inside it.  It's generated by using the new "ptext" export.

    An advantage of this new setup is that you can get the renderer to do output
    directly (by passing in a function of type (TextDetails -> IO () -> IO ()),
    rather than producing a string that you then print.


Version 2.0     24 April 1997
  * Made empty into a left unit for <> as well as a right unit;
    it is also now true that
        nest k empty = empty
    which wasn't true before.

  * Fixed an obscure bug in sep that occassionally gave very wierd behaviour

  * Added $+$

  * Corrected and tidied up the laws and invariants

======================================================================
Relative to John's original paper, there are the following new features:

1.  There's an empty document, "empty".  It's a left and right unit for 
    both <> and $$, and anywhere in the argument list for
    sep, hcat, hsep, vcat, fcat etc.

    It is Really Useful in practice.

2.  There is a paragraph-fill combinator, fsep, that's much like sep,
    only it keeps fitting things on one line until itc can't fit any more.

3.  Some random useful extra combinators are provided.  
        <+> puts its arguments beside each other with a space between them,
            unless either argument is empty in which case it returns the other


        hcat is a list version of <>
        hsep is a list version of <+>
        vcat is a list version of $$

        sep (separate) is either like hsep or like vcat, depending on what fits

        cat  is behaves like sep,  but it uses <> for horizontal conposition
        fcat is behaves like fsep, but it uses <> for horizontal conposition

        These new ones do the obvious things:
                char, semi, comma, colon, space,
                parens, brackets, braces, 
                quotes, doubleQuotes
        
4.      The "above" combinator, $$, now overlaps its two arguments if the
        last line of the top argument stops before the first line of the second begins.
        For example:  text "hi" $$ nest 5 "there"
        lays out as
                        hi   there
        rather than
                        hi
                             there

        There are two places this is really useful

        a) When making labelled blocks, like this:
                Left ->   code for left
                Right ->  code for right
                LongLongLongLabel ->
                          code for longlonglonglabel
           The block is on the same line as the label if the label is
           short, but on the next line otherwise.

        b) When laying out lists like this:
                [ first
                , second
                , third
                ]
           which some people like.  But if the list fits on one line
           you want [first, second, third].  You can't do this with
           John's original combinators, but it's quite easy with the
           new $$.

        The combinator $+$ gives the original "never-overlap" behaviour.

5.      Several different renderers are provided:
                * a standard one
                * one that uses cut-marks to avoid deeply-nested documents 
                        simply piling up in the right-hand margin
                * one that ignores indentation (fewer chars output; good for machines)
                * one that ignores indentation and newlines (ditto, only more so)

6.      Numerous implementation tidy-ups
        Use of unboxed data types to speed up the implementation



\begin{code}
module Pretty (
        Doc,            -- Abstract
        Mode(..),
	TextDetails(..),

        empty,		-- :: Doc
	isEmpty,	-- :: Doc -> Bool
	nest,		-- :: Int -> Doc -> Doc

        text,		-- :: String -> Doc
	ptext,		-- :: String -> Doc
	char,		-- :: Char   -> Doc

	sp_text,        -- :: String -> Int -> Doc

        int,		-- :: Int     -> Doc
	integer,	-- :: Integer -> Doc
	float,		-- :: Float   -> Doc
	double,		-- :: Double  -> Doc
	rational,	-- :: Ration  -> Doc

        parens,		-- :: Doc     -> Doc
	brackets,	-- :: Doc     -> Doc
	braces,		-- :: Doc     -> Doc
	quotes,		-- :: Doc     -> Doc
	doubleQuotes,	-- :: Doc     -> Doc
	
	spaces,         -- :: Int     -> Doc -> Doc

        semi,		-- :: Doc
	comma,		-- :: Doc
	colon,	 	-- :: Doc
	space,		-- :: Doc
	equals,		-- :: Doc
        lparen, rparen, -- :: Doc
	lbrack, rbrack, -- :: Doc
	lbrace, rbrace, -- :: Doc

        (<>),		-- :: Doc -> Doc -> Doc (beside)
	(<+>),		-- :: Doc -> Doc -> Doc (beside w/space)
	hcat,		-- :: [Doc] -> Doc      (list version of <>)
	hsep, 		-- :: [Doc] -> Doc      (list version of <+>)

        ($$),		-- :: Doc -> Doc -> Doc (above)
	($+$),  	-- :: Doc -> Doc -> Doc (above, no overlap)
	vcat,		-- :: Doc -> Doc -> Doc (list version of $$)

	cat, 		-- :: [Doc] -> Doc (either hcat or vcat)
        sep,		-- :: [Doc] -> Doc (either hsep or vsep)

        fsep,		-- :: [Doc] -> Doc  ('paragraph'-versions of the prev 2)
	fcat, 		-- :: [Doc] -> Doc

        hang,		-- :: Doc   -> Int -> Doc -> Doc
	punctuate,      -- :: Doc   -> [Doc] -> [Doc]
        
        render, 		-- :: Doc -> String
        renderStyle,		-- :: Style -> Doc -> String

	Style( mode		-- :: Mode
	     , lineLength       -- :: Int
	     , ribbonsPerLine   -- :: Float (ribbon length / line length)
	     ), 
	style,			-- :: Style  (default)

	fullRender		-- :: Mode
				-- -> Int
				-- -> Float
				-- -> (TextDetails -> a -> a)
				-- -> a
				-- -> Doc
				-- -> a
  ) where

infixl 6 <> 
infixl 6 <+>
infixl 5 $$, $+$
\end{code}

*********************************************************
*                                                       *
\subsection{The interface}
*                                                       *
*********************************************************

The primitive @Doc@ values

\begin{code}
empty                     :: Doc
isEmpty                   :: Doc    -> Bool
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
\end{code}

Combining @Doc@ values

\begin{code}
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
\end{code}

GHC-specific ones.

\begin{code}
hang :: Doc -> Int -> Doc -> Doc
punctuate :: Doc -> [Doc] -> [Doc]      -- punctuate p [d1, ... dn] = [d1 <> p, d2 <> p, ... dn-1 <> p, dn]
\end{code}

Displaying @Doc@ values. 

\begin{code}
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

data Style
 = Style { mode           :: Mode
 	 , lineLength     :: Int      -- In chars
         , ribbonsPerLine :: Float    -- Ratio of ribbon length to line length
         }

style :: Style          -- The default style
style = Style { lineLength = 100, ribbonsPerLine = 1.5, mode = PageMode }

data Mode = PageMode            -- Normal 
          | ZigZagMode          -- With zig-zag cuts
          | LeftMode            -- No indentation, infinitely long lines
          | OneLineMode         -- All on one line

\end{code}


*********************************************************
*                                                       *
\subsection{The @Doc@ calculus}
*                                                       *
*********************************************************

The @Doc@ combinators satisfy the following laws:
\begin{verbatim}
Laws for $$
~~~~~~~~~~~
<a1>    (x $$ y) $$ z   = x $$ (y $$ z)
<a2>    empty $$ x      = x
<a3>    x $$ empty      = x

        ...ditto $+$...

Laws for <>
~~~~~~~~~~~
<b1>    (x <> y) <> z   = x <> (y <> z)
<b2>    empty <> x      = empty
<b3>    x <> empty      = x

        ...ditto <+>...

Laws for text
~~~~~~~~~~~~~
<t1>    text s <> text t        = text (s++t)
<t2>    text "" <> x            = x, if x non-empty

Laws for nest
~~~~~~~~~~~~~
<n1>    nest 0 x                = x
<n2>    nest k (nest k' x)      = nest (k+k') x
<n3>    nest k (x <> y)         = nest k z <> nest k y
<n4>    nest k (x $$ y)         = nest k x $$ nest k y
<n5>    nest k empty            = empty
<n6>    x <> nest k y           = x <> y, if x non-empty

** Note the side condition on <n6>!  It is this that
** makes it OK for empty to be a left unit for <>.

Miscellaneous
~~~~~~~~~~~~~
<m1>    (text s <> x) $$ y = text s <> ((text "" <> x)) $$ 
                                         nest (-length s) y)

<m2>    (x $$ y) <> z = x $$ (y <> z)
        if y non-empty


Laws for list versions
~~~~~~~~~~~~~~~~~~~~~~
<l1>    sep (ps++[empty]++qs)   = sep (ps ++ qs)
        ...ditto hsep, hcat, vcat, fill...

<l2>    nest k (sep ps) = sep (map (nest k) ps)
        ...ditto hsep, hcat, vcat, fill...

Laws for oneLiner
~~~~~~~~~~~~~~~~~
<o1>    oneLiner (nest k p) = nest k (oneLiner p)
<o2>    oneLiner (x <> y)   = oneLiner x <> oneLiner y 
\end{verbatim}


You might think that the following verion of <m1> would
be neater:
\begin{verbatim}
<3 NO>  (text s <> x) $$ y = text s <> ((empty <> x)) $$ 
                                         nest (-length s) y)
\end{verbatim}
But it doesn't work, for if x=empty, we would have
\begin{verbatim}
        text s $$ y = text s <> (empty $$ nest (-length s) y)
                    = text s <> nest (-length s) y
\end{verbatim}



*********************************************************
*                                                       *
\subsection{Simple derived definitions}
*                                                       *
*********************************************************

\begin{code}
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

quotes p        = char '`' <> p <> char '\''
doubleQuotes p  = char '"' <> p <> char '"'
parens p        = char '(' <> p <> char ')'
brackets p      = char '[' <> p <> char ']'
braces p        = char '{' <> p <> char '}'

hcat = foldr (<>)  empty
hsep = foldr (<+>) empty
vcat = foldr ($$)  empty

hang d1 n d2 = sep [d1, nest n d2]

punctuate p []     = []
punctuate p (d:ds) = go d ds
                   where
                     go d [] = [d]
                     go d (e:es) = (d <> p) : go e es
\end{code}


*********************************************************
*                                                       *
\subsection{The @Doc@ data type}
*                                                       *
*********************************************************

A @Doc@ represents a {\em set} of layouts.  A @Doc@ with
no occurrences of @Union@ or @NoDoc@ represents just one layout.
\begin{code}
data Doc
 = Empty                                -- empty
 | NilAbove Doc                         -- text "" $$ x
 | TextBeside TextDetails !Int Doc      -- text s <> x  
 | Nest !Int Doc                        -- nest k x
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
\end{code}

Here are the invariants:
\begin{itemize}
\item
The argument of @NilAbove@ is never @Empty@. Therefore
a @NilAbove@ occupies at least two lines.

\item
The arugment of @TextBeside@ is never @Nest@.

\item 
The layouts of the two arguments of @Union@ both flatten to the same string.

\item 
The arguments of @Union@ are either @TextBeside@, or @NilAbove@.

\item
The right argument of a union cannot be equivalent to the empty set (@NoDoc@).
If the left argument of a union is equivalent to the empty set (@NoDoc@),
then the @NoDoc@ appears in the first line.

\item 
An empty document is always represented by @Empty@.
It can't be hidden inside a @Nest@, or a @Union@ of two @Empty@s.

\item 
The first line of every layout in the left argument of @Union@
is longer than the first line of any layout in the right argument.
(1) ensures that the left argument has a first line.  In view of (3),
this invariant means that the right argument must have at least two
lines.
\end{itemize}

\begin{code}
        -- Arg of a NilAbove is always an RDoc
nilAbove_ p = NilAbove p

        -- Arg of a TextBeside is always an RDoc
textBeside_ s sl p = TextBeside s sl p

        -- Arg of Nest is always an RDoc
nest_ k p = Nest k p

        -- Args of union are always RDocs
union_ p q = Union p q

\end{code}


Notice the difference between
        * NoDoc (no documents)
        * Empty (one empty document; no height and no width)
        * text "" (a document containing the empty string;
                   one line high, but has no width)



*********************************************************
*                                                       *
\subsection{@empty@, @text@, @nest@, @union@}
*                                                       *
*********************************************************

\begin{code}
empty = Empty

isEmpty Empty = True
isEmpty _     = False

char  c = textBeside_ (Chr c) 1 Empty
text  s = case length   s of {sl -> textBeside_ (Str s)  sl Empty}
ptext s = case length s of {sl -> textBeside_ (PStr s) sl Empty}

nest k  p = mkNest k (reduceDoc p)        -- Externally callable version

-- mkNest checks for Nest's invariant that it doesn't have an Empty inside it
mkNest k       _           | k `seq` False = undefined
mkNest k       (Nest k1 p) = mkNest (k + k1) p
mkNest k       NoDoc       = NoDoc
mkNest k       Empty       = Empty
mkNest 0       p           = p                  -- Worth a try!
mkNest k       p           = nest_ k p

-- mkUnion checks for an empty document
mkUnion Empty q = Empty
mkUnion p q     = p `union_` q
\end{code}

*********************************************************
*                                                       *
\subsection{additional primitive Doc}
*                                                       *
*********************************************************

added by Klaus L�ttich

the primitive command sp_text can be used for a special use of this
library. This function enables the possibility to use the rendering
alghorithms provided for rendering LaTeX with a proportional font. It
can also be abused because you can add text that has a zero width.


\begin{code}

sp_text :: Int -> String -> Doc
sp_text sl s = case sl of {sl1 -> textBeside_ (PStr s) sl1 Empty}
\end{code}

*********************************************************
*                                                       *
\subsection{Vertical composition @$$@}
*                                                       *
*********************************************************


\begin{code}
p $$  q = Above p False q
p $+$ q = Above p True q

above :: Doc -> Bool -> RDoc -> RDoc
above (Above p g1 q1)  g2 q2 = above p g1 (above q1 g2 q2)
above p@(Beside _ _ _) g  q  = aboveNest (reduceDoc p) g 0 (reduceDoc q)
above p g q                  = aboveNest p             g 0 (reduceDoc q)

aboveNest :: RDoc -> Bool -> Int -> RDoc -> RDoc
-- Specfication: aboveNest p g k q = p $g$ (nest k q)

aboveNest _                   _ k _ | k `seq` False = undefined
aboveNest NoDoc               g k q = NoDoc
aboveNest (p1 `Union` p2)     g k q = aboveNest p1 g k q `union_` 
                                      aboveNest p2 g k q
                                
aboveNest Empty               g k q = mkNest k q
aboveNest (Nest k1 p)         g k q = nest_ k1 (aboveNest p g (k - k1) q)
                                  -- p can't be Empty, so no need for mkNest
                                
aboveNest (NilAbove p)        g k q = nilAbove_ (aboveNest p g k q)
aboveNest (TextBeside s sl p) g k q = k1 `seq` textBeside_ s sl rest
                                    where
                                      k1   = k - sl
                                      rest = case p of
                                                Empty -> nilAboveNest g k1 q
                                                other -> aboveNest  p g k1 q
\end{code}

\begin{code}
nilAboveNest :: Bool -> Int -> RDoc -> RDoc
-- Specification: text s <> nilaboveNest g k q 
--              = text s <> (text "" $g$ nest k q)

nilAboveNest _ k _           | k `seq` False = undefined
nilAboveNest g k Empty       = Empty    -- Here's why the "text s <>" is in the spec!
nilAboveNest g k (Nest k1 q) = nilAboveNest g (k + k1) q

nilAboveNest g k q           | (not g) && (k > 0)        -- No newline if no overlap
                             = textBeside_ (Str (spaces k)) k q
                             | otherwise                        -- Put them really above
                             = nilAbove_ (mkNest k q)
\end{code}


*********************************************************
*                                                       *
\subsection{Horizontal composition @<>@}
*                                                       *
*********************************************************

\begin{code}
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
\end{code}

\begin{code}
nilBeside :: Bool -> RDoc -> RDoc
-- Specification: text "" <> nilBeside g p 
--              = text "" <g> p

nilBeside g Empty      = Empty  -- Hence the text "" in the spec
nilBeside g (Nest _ p) = nilBeside g p
nilBeside g p          | g         = textBeside_ space_text 1 p
                       | otherwise = p
\end{code}

*********************************************************
*                                                       *
\subsection{Separate, @sep@, Hughes version}
*                                                       *
*********************************************************

\begin{code}
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
sep1 g _                   k ys | k `seq` False = undefined
sep1 g NoDoc               k ys = NoDoc
sep1 g (p `Union` q)       k ys = sep1 g p k ys
                                  `union_`
                                  (aboveNest q False k (reduceDoc (vcat ys)))

sep1 g Empty               k ys = mkNest k (sepX g ys)
sep1 g (Nest n p)          k ys = nest_ n (sep1 g p (k - n) ys)

sep1 g (NilAbove p)        k ys = nilAbove_ (aboveNest p False k (reduceDoc (vcat ys)))
sep1 g (TextBeside s sl p) k ys = textBeside_ s sl (sepNB g p (k - sl) ys)

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
\end{code}

*********************************************************
*                                                       *
\subsection{@fill@}
*                                                       *
*********************************************************

\begin{code}
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
fill1 g _                   k ys | k `seq` False = undefined
fill1 g NoDoc               k ys = NoDoc
fill1 g (p `Union` q)       k ys = fill1 g p k ys
                                   `union_`
                                   (aboveNest q False k (fill g ys))

fill1 g Empty               k ys = mkNest k (fill g ys)
fill1 g (Nest n p)          k ys = nest_ n (fill1 g p (k - n) ys)

fill1 g (NilAbove p)        k ys = nilAbove_ (aboveNest p False k (fill g ys))
fill1 g (TextBeside s sl p) k ys = textBeside_ s sl (fillNB g p (k - sl) ys)

fillNB g _           k ys | k `seq` False = undefined
fillNB g (Nest _ p)  k ys  = fillNB g p k ys
fillNB g Empty k []        = Empty
fillNB g Empty k (y:ys)    = nilBeside g (fill1 g (oneLiner (reduceDoc y)) k1 ys)
                             `mkUnion` 
                             nilAboveNest False k (fill g (y:ys))
                           where
                             k1 | g         = k - 1
                                | otherwise = k

fillNB g p k ys            = fill1 g p k ys
\end{code}


*********************************************************
*                                                       *
\subsection{Selecting the best layout}
*                                                       *
*********************************************************

\begin{code}
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

best mode w r p
  = get w p
  where
    get :: Int          -- (Remaining) width of line
        -> Doc -> Doc
    get w _ | w==0 && False   = undefined
    get w Empty               = Empty
    get w NoDoc               = NoDoc
    get w (NilAbove p)        = nilAbove_ (get w p)
    get w (TextBeside s sl p) = textBeside_ s sl (get1 w sl p)
    get w (Nest k p)          = nest_ k (get (w - k) p)
    get w (p `Union` q)       = nicest w r (get w p) (get w q)

    get1 :: Int         -- (Remaining) width of line
         -> Int         -- Amount of first line already eaten up
         -> Doc         -- This is an argument to TextBeside => eat Nests
         -> Doc         -- No unions in here!

    get1 w _ _ | w==0 && False = undefined
    get1 w sl Empty               = Empty
    get1 w sl NoDoc               = NoDoc
    get1 w sl (NilAbove p)        = nilAbove_ (get (w - sl) p)
    get1 w sl (TextBeside t tl p) = textBeside_ t tl (get1 w (sl + tl) p)
    get1 w sl (Nest k p)          = get1 w sl p
    get1 w sl (p `Union` q)       = nicest1 w r sl (get1 w sl p) 
                                                   (get1 w sl q)

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
\end{code}

@first@ and @nonEmptySet@ are similar to @nicest@ and @fits@, only simpler.
@first@ returns its first argument if it is non-empty, otherwise its second.

\begin{code}
first p q | nonEmptySet p = p 
          | otherwise     = q

nonEmptySet NoDoc           = False
nonEmptySet (p `Union` q)      = True
nonEmptySet Empty              = True
nonEmptySet (NilAbove p)       = True           -- NoDoc always in first line
nonEmptySet (TextBeside _ _ p) = nonEmptySet p
nonEmptySet (Nest _ p)         = nonEmptySet p
\end{code}

@oneLiner@ returns the one-line members of the given set of @Doc@s.

\begin{code}
oneLiner :: Doc -> Doc
oneLiner NoDoc               = NoDoc
oneLiner Empty               = Empty
oneLiner (NilAbove p)        = NoDoc
oneLiner (TextBeside s sl p) = textBeside_ s sl (oneLiner p)
oneLiner (Nest k p)          = nest_ k (oneLiner p)
oneLiner (p `Union` q)       = oneLiner p
\end{code}



*********************************************************
*                                                       *
\subsection{Displaying the best layout}
*                                                       *
*********************************************************


\begin{code}
renderStyle (Style mode lineLength ribbonsPerLine) doc 
  = fullRender mode lineLength ribbonsPerLine string_txt "" doc

render doc       = showDoc doc ""
showDoc doc rest = fullRender PageMode 100 1.5 string_txt rest doc

string_txt (Chr c)   s  = c:s
string_txt (Str s1)  s2 = s1 ++ s2
string_txt (PStr s1) s2 = s1 ++ s2
\end{code}

\begin{code}

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
        lay k _            | k `seq` False = undefined
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
    
        lay1 k _ sl _ | k+sl `seq` False = undefined
        lay1 k s sl p = Str (indent k) `txt` (s `txt` lay2 (k + sl) p)
    
        lay2 k _ | k `seq` False = undefined
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

indent n | n >= 8     = '\t' : indent (n - 8)
         | otherwise  = spaces n

multi_ch n ch = replicate n ch
spaces n = replicate n ' '
\end{code}

