-----------------------------------------------------------
-- Daan Leijen (c) 2000, http://www.cs.uu.nl/~daan
--
-- Pretty print module based on Philip Wadlers "prettier printer"
--      "A prettier printer"
--      Draft paper, April 1997, revised March 1998. 
--      http://cm.bell-labs.com/cm/cs/who/wadler/papers/prettier/prettier.ps
--
-- Haskell98 compatible
-----------------------------------------------------------
module Shell.PPrint 
        ( Doc
        , Pretty, pretty
        
        , show, putDoc, hPutDoc
        
        , (<>)
        , (<+>)
        , (</>), (<//>)
        , (<$>), (<$$>)
        
        , sep, fillSep, hsep, vsep
        , cat, fillCat, hcat, vcat
        , punctuate
        
        , align, hang, indent
        , fill, fillBreak
        
        , list, tupled, semiBraces, encloseSep
        , angles, langle, rangle
        , parens, lparen, rparen
        , braces, lbrace, rbrace
        , brackets, lbracket, rbracket
        , dquotes, dquote, squotes, squote
        
        , comma, space, dot, backslash
        , semi, colon, equals
        
        , string, bool, int, integer, float, double, rational
        
        , softline, softbreak
        , empty, char, text, line, linebreak, nest, group        
        , column, nesting, width        
        
        , SimpleDoc(..)
        , renderPretty, renderCompact
        , displayS, displayIO                
        ) where

import IO      (Handle,hPutStr,hPutChar,stdout)

infixr 5 </>,<//>,<$>,<$$>
infixr 6 <>,<+>


-----------------------------------------------------------
-- list, tupled and semiBraces pretty print a list of
-- documents either horizontally or vertically aligned.
-----------------------------------------------------------
list :: [Doc] -> Doc
list            = encloseSep lbracket rbracket comma

tupled :: [Doc]-> Doc
tupled          = encloseSep lparen   rparen  comma

semiBraces :: [Doc] -> Doc
semiBraces      = encloseSep lbrace   rbrace  semi

encloseSep :: Doc -> Doc -> Doc -> [Doc] ->Doc
encloseSep left right nwsep ds
    = case ds of
        []  -> left <> right
        [d] -> left <> d <> right
        _   -> align (cat (zipWith (<>) (left : repeat nwsep) ds) <> right) 


-----------------------------------------------------------
-- punctuate p [d1,d2,...,dn] => [d1 <> p,d2 <> p, ... ,dn]
-----------------------------------------------------------
punctuate :: Doc -> [Doc] -> [Doc]
punctuate _ []      = []
punctuate _ [d]     = [d]
punctuate p (d:ds)  = (d <> p) : punctuate p ds

                   
-----------------------------------------------------------
-- high-level combinators
-----------------------------------------------------------
sep :: [Doc] -> Doc
sep             = group . vsep

fillSep :: [Doc] -> Doc
fillSep         = fold (</>)

hsep :: [Doc]-> Doc
hsep            = fold (<+>)

vsep :: [Doc]-> Doc
vsep            = fold (<$>) 


cat :: [Doc]->Doc
cat             = group . vcat

fillCat :: [Doc]->Doc
fillCat         = fold (<//>)

hcat :: [Doc]->Doc
hcat            = fold (<>)

vcat :: [Doc]-> Doc
vcat            = fold (<$$>) 


fold :: (Doc -> Doc -> Doc)-> [Doc]-> Doc
fold _ []       = empty
fold f ds       = foldr1 f ds

(<>) :: Doc -> Doc -> Doc
x <> y          = x `beside` y

(<+>) :: Doc -> Doc -> Doc
x <+> y         = x <> space <> y

(</>) :: Doc -> Doc -> Doc
x </> y         = x <> softline <> y

(<//>) :: Doc -> Doc -> Doc
x <//> y        = x <> softbreak <> y   

(<$>) :: Doc -> Doc -> Doc
x <$> y         = x <> line <> y

(<$$>) :: Doc -> Doc -> Doc
x <$$> y        = x <> linebreak <> y


softline :: Doc
softline        = group line

softbreak :: Doc
softbreak       = group linebreak

squotes :: Doc -> Doc
squotes         = enclose squote squote
dquotes :: Doc -> Doc
dquotes         = enclose dquote dquote
braces :: Doc -> Doc
braces          = enclose lbrace rbrace
parens :: Doc -> Doc
parens          = enclose lparen rparen
angles :: Doc -> Doc
angles          = enclose langle rangle
brackets :: Doc -> Doc
brackets        = enclose lbracket rbracket
enclose :: Doc -> Doc -> Doc -> Doc
enclose l r x   = l <> x <> r

lparen :: Doc
lparen          = char '('
rparen :: Doc
rparen          = char ')'
langle :: Doc
langle          = char '<'
rangle :: Doc
rangle          = char '>'
lbrace :: Doc
lbrace          = char '{'
rbrace :: Doc
rbrace          = char '}'
lbracket :: Doc
lbracket        = char '['
rbracket :: Doc
rbracket        = char ']'

squote :: Doc
squote          = char '\''
dquote :: Doc
dquote          = char '"'
semi :: Doc
semi            = char ';'
colon :: Doc
colon           = char ':'
comma :: Doc
comma           = char ','
space :: Doc
space           = char ' '
dot :: Doc
dot             = char '.'
backslash :: Doc
backslash       = char '\\'
equals :: Doc
equals          = char '='


-----------------------------------------------------------
-- Combinators for prelude types
-----------------------------------------------------------

-- string is like "text" but replaces '\n' by "line"
string :: [Char] -> Doc
string ""       = empty
string ('\n':s) = line <> string s
string s        = case (span (/='\n') s) of
                    (xs,ys) -> text xs <> string ys
                  

bool :: Bool -> Doc
bool b          = text (show b)

int :: Int -> Doc                  
int i           = text (show i)

integer :: Integer -> Doc
integer i       = text (show i)

float :: Float -> Doc
float f         = text (show f)

double :: Double -> Doc
double d        = text (show d)

rational :: Rational -> Doc
rational r      = text (show r)
                  
                                                     
-----------------------------------------------------------
-- overloading "pretty"
-----------------------------------------------------------
class Pretty a where
  pretty        :: a -> Doc 
  prettyList    :: [a] -> Doc
  prettyList    = list . map pretty

instance Pretty a => Pretty [a] where
  pretty        = prettyList
  
instance Pretty Doc where
  pretty        = id  
  
instance Pretty () where
  pretty ()     = text "()"

instance Pretty Bool where
  pretty b      = bool b
  
instance Pretty Char where
  pretty c      = char c
  prettyList s  = string s
    
instance Pretty Int where
  pretty i      = int i
  
instance Pretty Integer where
  pretty i      = integer i

instance Pretty Float where
  pretty f      = float f

instance Pretty Double where
  pretty d      = double d
  

--instance Pretty Rational where
--  pretty r      = rational r  

instance (Pretty a,Pretty b) => Pretty (a,b) where
  pretty (x,y)  = tupled [pretty x, pretty y]

instance (Pretty a,Pretty b,Pretty c) => Pretty (a,b,c) where
  pretty (x,y,z)= tupled [pretty x, pretty y, pretty z]

instance Pretty a => Pretty (Maybe a) where
  pretty Nothing        = empty
  pretty (Just x)       = pretty x
  


-----------------------------------------------------------
-- semi primitive: fill and fillBreak 
-----------------------------------------------------------
fillBreak :: Int -> Doc -> Doc
fillBreak f x   = width x (\w ->
                  if (w > f) then nest f linebreak 
                             else text (spaces (f - w)))

fill :: Int -> Doc -> Doc    
fill f d        = width d (\w ->
                  if (w >= f) then empty
                              else text (spaces (f - w)))

width :: Doc -> (Int -> Doc) -> Doc        
width d f       = column (\k1 -> d <> column (\k2 -> f (k2 - k1)))        
        

-----------------------------------------------------------
-- semi primitive: Alignment and indentation
-----------------------------------------------------------
indent :: Int -> Doc -> Doc
indent i d      = hang i (text (spaces i) <> d)

hang :: Int -> Doc -> Doc
hang i d        = align (nest i d)

align :: Doc -> Doc
align d         = column (\k ->
                  nesting (\i -> nest (k - i) d))   --nesting might be negative :-)



-----------------------------------------------------------
-- Primitives
-----------------------------------------------------------
data Doc        = Empty
                | Char Char             -- invariant: char is not '\n'
                | Text !Int String      -- invariant: text doesn't contain '\n'
                | Line !Bool            -- True <=> when undone by group, do not insert a space 
                | Cat Doc Doc
                | Nest !Int Doc
                | Union Doc Doc         -- invariant: first lines of first doc longer than the first lines of the second doc
                | Column  (Int -> Doc)
                | Nesting (Int -> Doc)
                
data SimpleDoc  = SEmpty
                | SChar Char SimpleDoc
                | SText !Int String SimpleDoc
                | SLine !Int SimpleDoc
                

empty :: Doc                
empty           = Empty

char :: Char -> Doc
char '\n'       = line
char c          = Char c

text :: [Char] -> Doc
text ""         = Empty
text s          = Text (length s) s

line :: Doc
line            = Line False
linebreak :: Doc
linebreak       = Line True

beside :: Doc -> Doc -> Doc
beside x y      = Cat x y
nest :: Int -> Doc -> Doc
nest i x        = Nest i x
column :: ( Int -> Doc ) -> Doc
column f        = Column f
nesting :: (Int -> Doc ) -> Doc
nesting f       = Nesting f     
group :: Doc -> Doc
group x         = Union (flatten x) x

flatten :: Doc -> Doc
flatten (Cat x y)       = Cat (flatten x) (flatten y)
flatten (Nest i x)      = Nest i (flatten x)
flatten (Line nwbreak)  = if nwbreak then Empty else Text 1 " "
flatten (Union x _)     = flatten x
flatten (Column f)      = Column (flatten . f)
flatten (Nesting f)     = Nesting (flatten . f)
flatten other           = other                     --Empty,Char,Text
  
  

-----------------------------------------------------------
-- Renderers
-----------------------------------------------------------

-----------------------------------------------------------
-- renderPretty: the default pretty printing algorithm
-----------------------------------------------------------

-- list of indentation/document pairs; saves an indirection over [(Int,Doc)]
data Docs   = Nil
            | Cons !Int Doc Docs

renderPretty :: Float -> Int -> Doc -> SimpleDoc
renderPretty rfrac w x      
    = best 0 0 (Cons 0 x Nil)                
    where
      -- r :: the ribbon width in characters
      r  = max 0 (min w (round (fromIntegral w * rfrac)))
      
      -- best :: n = indentation of current line
      --         k = current column  
      --        (ie. (k >= n) && (k - n == count of inserted characters)
      best _ _ Nil      = SEmpty
      best n k (Cons i d ds)  
        = case d of
            Empty       -> best n k ds                
            Char c      -> let k' = k+1 in seq k' (SChar c (best n k' ds))
            Text l s    -> let k' = k+l in seq k' (SText l s (best n k' ds))
            Line _      -> SLine i (best i i ds)                 
            Cat nwx y   -> best n k (Cons i nwx (Cons i y ds))                
            Nest j nwx  -> let i' = i+j in seq i' (best n k (Cons i' nwx ds))
            Union nwx y -> nicest n k (best n k (Cons i nwx ds))                
                                      (best n k (Cons i y ds))                

            Column f    -> best n k (Cons i (f k) ds)
            Nesting f   -> best n k (Cons i (f i) ds)                            

      --nicest :: r = ribbon width, w = page width, 
      --          n = indentation of current line, k = current column
      --          x and y, the (simple) documents to chose from.
      --          precondition: first lines of x are longer than the first lines of y.                                      
      nicest n k nwx y  | fits nwidth nwx  = nwx
                        | otherwise     = y
                        where
                          nwidth = min (w - k) (r - k + n)
  

fits :: Int -> SimpleDoc -> Bool                                                                                      
fits w _        | w < 0         = False
fits _ SEmpty                   = True
fits w (SChar _ x)              = fits (w - 1) x                  
fits w (SText l _ x)            = fits (w - l) x
fits _ (SLine _ _)              = True


-----------------------------------------------------------
-- renderCompact: renders documents without indentation
--  fast and fewer characters output, good for machines
-----------------------------------------------------------
renderCompact :: Doc -> SimpleDoc
renderCompact x   
    = scan 0 [x]
    where
      scan _ []     = SEmpty
      scan k (d:ds) = case d of
                        Empty       -> scan k ds
                        Char c      -> let k' = k+1 in seq k' (SChar c (scan k' ds))
                        Text l s    -> let k' = k+l in seq k' (SText l s (scan k' ds))
                        Line _      -> SLine 0 (scan 0 ds)    
                        Cat nx y    -> scan k (nx:y:ds)
                        Nest _ nx   -> scan k (nx:ds)
                        Union _ y   -> scan k (y:ds)
                        Column f    -> scan k (f k:ds)
                        Nesting f   -> scan k (f 0:ds)



-----------------------------------------------------------
-- Displayers:  displayS and displayIO
-----------------------------------------------------------
displayS :: SimpleDoc -> ShowS
displayS SEmpty             = id
displayS (SChar c x)        = showChar c . displayS x
displayS (SText _ s x)      = showString s . displayS x
displayS (SLine i x)        = showString ('\n':indentation i) . displayS x

displayIO :: Handle -> SimpleDoc -> IO ()
displayIO handle simpleDoc
    = display simpleDoc
    where
      display SEmpty        = return ()
      display (SChar c x)   = do{ hPutChar handle c; display x}  
      display (SText _ s x) = do{ hPutStr handle s; display x}
      display (SLine i x)   = do{ hPutStr handle ('\n':indentation i); display x}


-----------------------------------------------------------
-- default pretty printers: show, putDoc and hPutDoc
-----------------------------------------------------------
instance Show Doc where
  showsPrec _ doc       = displayS (renderPretty 0.4 80 doc)

putDoc :: Doc -> IO ()
putDoc doc              = hPutDoc stdout doc

hPutDoc :: Handle -> Doc -> IO ()
hPutDoc handle doc      = displayIO handle (renderPretty 0.4 80 doc)



-----------------------------------------------------------
-- insert spaces
-- "indentation" used to insert tabs but tabs seem to cause
-- more trouble than they solve :-) 
-----------------------------------------------------------
spaces :: Int -> [Char]
spaces n        | n <= 0    = ""
                | otherwise = replicate n ' '

indentation :: Int -> [Char]
indentation n   = spaces n

--indentation n   | n >= 8    = '\t' : indentation (n-8)
--                | otherwise = spaces n
