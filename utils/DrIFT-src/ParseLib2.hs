{-----------------------------------------------------------------------------

                 A LIBRARY OF MONADIC PARSER COMBINATORS

                              29th July 1996
                           Revised, October 1996

                 Graham Hutton               Erik Meijer
            University of Nottingham    University of Utrecht

This Haskell 1.4 script defines a library of parser combinators, and is taken
from sections 1-6 of our article "Monadic Parser Combinators".  Some changes
to the library have been made in the move from Gofer to Haskell:

   * Do notation is used in place of monad comprehension notation;

   * The parser datatype is defined using "newtype", to avoid the overhead
     of tagging and untagging parsers with the P constructor.

-----------------------------------------------------------------------------}
-- Added to April 1997, for offside rule, {- -} comments, annotations, 
-- extra characters in identifiers .. - 
-- extra combinator parsers for skipping over input


module ParseLib2
   (Parser, item, papply, (+++), sat, many, many1, sepby, sepby1, chainl,
    chainl1, chainr, chainr1, ops, bracket, char, digit, lower, upper,
    letter, alphanum, string, ident, nat, int, spaces, comment, junk,
    parse, token, natural, integer, symbol, identifier,
    many1_offside,many_offside,off,
    opt, skipUntil, skipUntilOff,skipUntilParse,skipNest) where

import Char 
import Monad

infixr 5 +++

--- The parser monad ---------------------------------------------------------

newtype Parser a   = P (Pos -> Pstring -> [(a,Pstring)])

type Pstring = (Pos,String)
type Pos = (Int,Int)

instance Functor Parser where
   -- fmap         :: (a -> b) -> (Parser a -> Parser b)
   fmap f (P p)     = P (\pos inp -> [(f v, out) | (v,out) <- p pos inp])

instance Monad Parser where
   -- return      :: a -> Parser a
   return v        = P (\pos inp -> [(v,inp)])

   -- >>=         :: Parser a -> (a -> Parser b) -> Parser b
   (P p) >>= f     = P (\pos inp -> concat [papply (f v) pos out 
						| (v,out) <- p pos inp])
   fail s          = P (\pos inp -> [])

instance MonadPlus Parser where
   -- mzero            :: Parser a
   mzero                = P (\pos inp -> [])
   -- mplus            :: Parser a -> Parser a -> Parser a
   (P p) `mplus` (P q)    = P (\pos inp -> (p pos inp ++ q pos inp))

-- bits which donn't fit into Haskell's type classes just yet :-(

env :: Parser Pos
env = P(\pos inp -> [(pos,inp)])

setenv :: Pos -> Parser a -> Parser a
setenv s (P m) = P $  \_ -> m s

update :: (Pstring -> Pstring) -> Parser Pstring
update f = P( \pos s -> [(s,f s)])

set :: Pstring -> Parser Pstring
set s = update (\_ -> s)

fetch :: Parser Pstring
fetch = update id 

--- Other primitive parser combinators ---------------------------------------

item              :: Parser Char
item = do (pos,x:_) <- update newstate
	  defpos <- env
	  if onside pos defpos then return x else mzero

force             :: Parser a -> Parser a
force (P p)        = P (\pos inp -> let x = p pos inp in
                                (fst (head x), snd (head x)) : tail x)

first             :: Parser a -> Parser a
first (P p)        = P (\pos inp -> case p pos inp of
                                   []     -> []
                                   (x:xs) -> [x])

papply            :: Parser a -> Pos -> Pstring -> [(a,Pstring)]
papply (P p) pos inp   = p pos inp

-- layout handling functions

onside :: Pos -> Pos -> Bool
onside (l,c) (dl,dc) = (c > dc) || (l == dl)

newstate :: Pstring -> Pstring
newstate ((l,c),x:xs) = ((l',c'),xs)
	where
	(l',c') = case x of
			'\n' -> (l+1,0)
			'\t' -> (l,((c `div` 8) +1)*8)
			_    -> (l,c+1)

--- Derived combinators ------------------------------------------------------

(+++)             :: Parser a -> Parser a -> Parser a
p +++ q            = first (p `mplus` q)

sat               :: (Char -> Bool) -> Parser Char
sat p              = do {x <- item; if p x then return x else mzero}

many              :: Parser a -> Parser [a]
--many p           = force (many1 p +++ return [])
many p             = (many1 p +++ return [])

many1             :: Parser a -> Parser [a]
many1 p            = do {x <- p; xs <- many p; return (x:xs)}

sepby             :: Parser a -> Parser b -> Parser [a]
p `sepby` sep      = (p `sepby1` sep) +++ return []

sepby1            :: Parser a -> Parser b -> Parser [a]
p `sepby1` sep     = do {x <- p; xs <- many (do {sep; p}); return (x:xs)}

chainl            :: Parser a -> Parser (a -> a -> a) -> a -> Parser a
chainl p op v      = (p `chainl1` op) +++ return v

chainl1           :: Parser a -> Parser (a -> a -> a) -> Parser a
p `chainl1` op     = do {x <- p; rest x}
                     where
                        rest x = do {f <- op; y <- p; rest (f x y)}
                                 +++ return x

chainr            :: Parser a -> Parser (a -> a -> a) -> a -> Parser a
chainr p op v      = (p `chainr1` op) +++ return v

chainr1           :: Parser a -> Parser (a -> a -> a) -> Parser a
p `chainr1` op     = do {x <- p; rest x}
                     where
                        rest x = do {f <- op; y <- p `chainr1` op; return (f x y)}
                                 +++ return x

ops               :: [(Parser a, b)] -> Parser b
ops xs             = foldr1 (+++) [do {p; return op} | (p,op) <- xs]

bracket           :: Parser a -> Parser b -> Parser c -> Parser b
bracket open p close = do {open; x <- p; close; return x}

--- Useful parsers -----------------------------------------------------------

char              :: Char -> Parser Char
char x             = sat (\y -> x == y)

digit             :: Parser Char
digit              = sat isDigit

lower             :: Parser Char
lower              = sat isLower

upper             :: Parser Char
upper              = sat isUpper

letter            :: Parser Char
letter             = sat isAlpha

alphanum          :: Parser Char
alphanum           = sat (\x -> isAlphaNum x || x `elem` ['\'','_','.','#'])

string            :: String -> Parser String
string ""          = return ""
string (x:xs)      = do {char x; string xs; return (x:xs)}

ident             :: Parser String
ident              = do {x <- lower; xs <- many alphanum; return (x:xs)}

nat               :: Parser Int
nat                = do {x <- digit; return (digitToInt x)} `chainl1` return op
                     where
                        m `op` n = 10*m + n

int               :: Parser Int
int                = do {char '-'; n <- nat; return (-n)} +++ nat

--- Lexical combinators ------------------------------------------------------

spaces            :: Parser ()
spaces             = do {many1 (sat isJunk); return ()}

isJunk x = isSpace x || (not . isPrint) x || isControl x
  
comment :: Parser ()
comment = onelinecomment `mplus` bracecomment

onelinecomment    :: Parser ()
onelinecomment     = do {string "--"; many (sat (\x -> x /= '\n')); return ()}

bracecomment      :: Parser ()
bracecomment = skipNest 
	 (do{string "{-"; sat (`notElem` ['!','@','*'])})
	 (do{sat (`notElem` ['!','@','*']);string "-}"})

junk              :: Parser ()
junk               = do _ <- setenv (0,-1) (many (spaces +++ comment))
                        return ()

parse             :: Parser a -> Parser a
parse p            = do {junk; p}

token             :: Parser a -> Parser a
token p            = do {v <- p; junk; return v}

--- Token parsers ------------------------------------------------------------

natural           :: Parser Int
natural            = token nat

integer           :: Parser Int
integer            = token int

symbol            :: String -> Parser String
symbol xs          = token (string xs)


identifier        :: [String] -> Parser String
identifier ks      = token (do {x <- ident; if not (elem x ks) then return x
                                                               else mzero})
--- Offside Parsers ---------------------------------------------------------

many1_offside :: Parser a -> Parser [a] 
many1_offside p = do (pos,_) <- fetch
		     vs <- setenv pos (many1 (off p))
                     return vs

many_offside :: Parser a -> Parser [a] 
many_offside p = many1_offside p +++ mzero


off :: Parser a -> Parser a
off p = do (dl,dc) <- env
	   ((l,c),_) <- fetch
	   if c == dc then setenv (l,dc) p else mzero


------------------------------------------------------------------------------
-- Noel's own favourite parsers

skipUntil :: Parser a -> Parser a
skipUntil p = p +++ do token (many1 (sat (not . isSpace)))
                       skipUntil p
			 
skipNest :: Parser a -> Parser b -> Parser ()
skipNest start finish  = let 
    x = do{ finish;return()} 
	+++ do{skipNest start finish;x} +++ do{item;x} 
    in do{start; x}
    
-- this are messy, but make writing incomplete parsers a whole lot
-- easier.
skipUntilOff :: Parser a -> Parser [a]
skipUntilOff p = fmap (concatMap justs) . many_offside $ 
        fmap Just p +++ fmap (const Nothing) (many1 (token (many1 item)))


skipUntilParse :: Char ->  Parser a  -> Parser [a]
skipUntilParse u p = fmap (concatMap justs) . many $
	do r<- p
           token (char u)
           return (Just r)
        +++
	do many . token . many1 . sat $(/= u)
           token (char u)
           return Nothing

justs (Just a)  = [a]
justs Nothing   = []


opt p = p +++ return [] 

