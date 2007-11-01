
module PPrel where

-- Standard types, classes, instances and related functions

-- Numeric classes

class  (Num a, Ord a) => RealK a  where
    toRational'       ::  a -> Rational


class  (RealK a, Enum a) => IntegralK a  where
    quot', rem'        :: a -> a -> a   
    div', mod'         :: a -> a -> a
    quotRem', divMod'  :: a -> a -> (a,a)
    toInteger'        :: a -> Integer

        -- Minimal complete definition:
        --      quotRem, toInteger
    n `quot'` d       =  fst (quotRem' n d)
    n `rem'` d        =  snd (quotRem' n d)
    n `div'` d        =  fst (divMod' n d)
    n `mod'` d        =  snd (divMod' n d)
    divMod' n d       =  let qr = quotRem' n d
                             q  = fst qr
                             r  = snd qr
                         in if signum r == (0 - signum d) then 
                            (q - 1, r + d) else quotRem' n d
-- if signum r == - signum d then (q-1, r+d) 
--                        else quotRem n d

class  (Num a) => FractionalK a  where
    (/#)              :: a -> a -> a
    recip'            :: a -> a
    fromRational'     :: Rational -> a

        -- Minimal complete definition:
        --      fromRational and (recip or (/))
    recip' x          =  1 /# x
    x /# y            =  x * recip' y

-- Numeric functions

-- subtract'         :: (Num a) => a -> a -> a
-- subtract'         =  flip' (-)

even', odd'       :: (IntegralK a) => a -> Bool
even' n           =  n `rem'` 2 == 0
odd'              =  not . even'

gcd'              :: (IntegralK a) => a -> a -> a
gcd' 0 0          =  error "Prelude.gcd: gcd 0 0 is undefined"
gcd' x y          =  gcdH (abs x) (abs y)

gcdH             :: (IntegralK a) => a -> a -> a
gcdH x 0  =  x
gcdH x y  =  gcdH y (x `rem'` y)

lcm'              :: (IntegralK a) => a -> a -> a
lcm' _ 0          =  0
lcm' 0 _          =  0
lcm' x y          =  abs ((x `quot'` (gcd' x y)) * y)

(^#)              :: (Num a, IntegralK b) => a -> b -> a
x ^# 0            =  1
x ^# n | n > 0    =  powAux x (n - 1) x
_ ^# _            =  error "Prelude.^: negative exponent"

powAux :: (Num a, IntegralK b) => a -> b -> a -> a
powAux _ 0 y = y
powAux x n y = powBux x n y
 
powBux :: (Num a, IntegralK b) => a -> b -> a -> a                    
powBux x n y | even' n  = powBux (x * x) (n `quot'` 2) y
            | otherwise' = powAux x (n - 1) (x * y)

(^^#)             :: (FractionalK a, IntegralK b) => a -> b -> a
x ^^# n           =  if n >= 0 then x ^# n else recip' (x ^# (0 - n))

fromIntegral'     :: (IntegralK a, Num b) => a -> b
fromIntegral'     =  fromInteger . toInteger'

realToFrac'     :: (RealK a, FractionalK b) => a -> b
realToFrac'      =  fromRational' . toRational'

-- Trivial type

-- data  ()  =  ()  deriving (Eq, Ord, Enum, Bounded)
-- Not legal Haskell; for illustration only

-- Function type

-- identity function

id'               :: a -> a
id' x             =  x

-- constant function

const'            :: a -> b -> a
const' x _        =  x

-- function composition

-- (.)              :: (b -> c) -> (a -> b) -> a -> c
-- f . g            =  \ x -> f (g x)

-- flip f  takes its (first) two arguments in the reverse order of f.

-- flip'             :: (a -> b -> c) -> b -> a -> c
-- flip' f x y       =  f y x

{-
seq :: a -> b -> b
seq = ...       -- Primitive
-}

-- right-associating infix application operators 
-- (useful in continuation-passing style)

-- ($), ($!) :: (a -> b) -> a -> b
-- f $  x    =  f x
-- f $! x    =  P.seq x (f x)

-- Boolean type

-- data  Bool  =  False | True     deriving (P.Eq, P.Ord, P.Enum, P.Bounded)

-- Boolean functions

otherwise'        :: Bool
otherwise'        =  True

-- primIntToChar = undefined'
-- primCharToInt = undefined'
-- primUnicodeMaxChar = undefined'

maybe'              :: b -> (a -> b) -> Maybe a -> b
maybe' n f Nothing  =  n
maybe' n f (Just x) =  f x

either'               :: (a -> c) -> (b -> c) -> Either a b -> c
either' f g (Left x)  =  f x
either' f g (Right y) =  g y

-- curry converts an uncurried function to a curried function;
-- uncurry converts a curried function to a function on pairs.

curry'            :: ((a, b) -> c) -> a -> b -> c
curry' f x y      =  f (x, y)

uncurry'          :: (a -> b -> c) -> ((a, b) -> c)
uncurry' f p      =  f (fst p) (snd p)

-- Misc functions

-- until p f  yields the result of applying f until p holds.

until'            :: (a -> Bool) -> (a -> a) -> a -> a
until' p f x 
     | p x       =  x
     | otherwise' =  until' p f (f x)

-- asTypeOf is a type-restricted version of const.  It is usually used
-- as an infix operator, and its typing forces its first argument
-- (which is usually overloaded) to have the same type as the second.

asTypeOf'         :: a -> a -> a
asTypeOf'         =  const'

-- error stops execution and displays an error message

-- error'            :: String -> a
-- error'            =  primError

-- It is expected that compilers will recognize this and insert error
-- messages that are more appropriate to the context in which undefined 
-- appears. 

undefined'        :: a
undefined'        =  error "Prelude.undefined"

-- Standard list functions

-- Map and append

head'             :: [a] -> a
head' (x:_)       =  x
head' []          =  error "Prelude.head: empty list"

tail'             :: [a] -> [a]
tail' (_:xs)      =  xs
tail' []          =  error "Prelude.tail: empty list"

-- map' :: (a -> b) -> [a] -> [b]
-- map' f []     = []
-- map' f (x:xs) = f x : map' f xs

(++#) :: [a] -> [a] -> [a]
[]     ++# ys = ys
(x:xs) ++# ys = x : (xs ++# ys)

filter' :: (a -> Bool) -> [a] -> [a]
filter' p []                 = []
filter' p (x:xs) | p x       = x : filter' p xs
                 | otherwise' = filter' p xs

concat' :: [[a]] -> [a]
concat' xss = foldr' (++#) [] xss

concatMap' :: (a -> [b]) -> [a] -> [b]
concatMap' f = concat' . map f

-- head and tail extract the first element and remaining elements,
-- respectively, of a list, which must be non-empty.  last and init
-- are the dual functions working from the end of a finite list,
-- rather than the beginning.

last'             :: [a] -> a
last' [x]         =  x
last' (_:xs)      =  last' xs
last' []          =  error "Prelude.last: empty list"

init'             :: [a] -> [a]
init' [x]         =  []
init' (x:xs)      =  x : init' xs
init' []          =  error "Prelude.init: empty list"

null'             :: [a] -> Bool
null' []          =  True
null' (_:_)       =  False

-- length returns the length of a finite list as an Int.

length'           :: [a] -> Int
length' []        =  0
length' (_:l)     =  1 + length' l

-- List index (subscript) operator, 0-origin

(!!#)                :: [a] -> Int -> a
xs     !!# n | n < 0 =  error "Prelude.!!: negative index"
[]     !!# _         =  error "Prelude.!!: index too large"
(x:_)  !!# 0         =  x
(_:xs) !!# n         =  xs !!# (n - 1)

-- foldl, applied to a binary operator, a starting value (typically the
-- left-identity of the operator), and a list, reduces the list using
-- the binary operator, from left to right:
--  foldl f z [x1, x2, ..., xn] == (...((z `f` x1) `f` x2) `f`...) `f` xn
-- foldl1 is a variant that has no starting value argument, and  thus must
-- be applied to non-empty lists.  scanl is similar to foldl, but returns
-- a list of successive reduced values from the left:
--      scanl f z [x1, x2, ...] == [z, z `f` x1, (z `f` x1) `f` x2, ...]
-- Note that  last (scanl f z xs) == foldl f z xs.
-- scanl1 is similar, again without the starting element:
--      scanl1 f [x1, x2, ...] == [x1, x1 `f` x2, ...]

foldl'            :: (a -> b -> a) -> a -> [b] -> a
foldl' f z []     =  z
foldl' f z (x:xs) =  foldl' f (f z x) xs

foldl1'           :: (a -> a -> a) -> [a] -> a
foldl1' f (x:xs)  =  foldl' f x xs
foldl1' _ []      =  error "Prelude.foldl1: empty list"

scanl'            :: (a -> b -> a) -> a -> [b] -> [a]
scanl' f q xs     =  q : (case xs of
                            []   -> []
                            x:xs -> scanl' f (f q x) xs)

scanl1'           :: (a -> a -> a) -> [a] -> [a]
scanl1' f (x:xs)  =  scanl' f x xs
scanl1' _ []      =  []

-- foldr, foldr1, scanr, and scanr1 are the right-to-left duals of the
-- above functions.

foldr'            :: (a -> b -> b) -> b -> [a] -> b
foldr' f z []     =  z
foldr' f z (x:xs) =  f x (foldr' f z xs)

foldr1'           :: (a -> a -> a) -> [a] -> a
foldr1' f [x]     =  x
foldr1' f (x:xs)  =  f x (foldr1' f xs)
foldr1' _ []      =  error "Prelude.foldr1: empty list"

scanr'             :: (a -> b -> b) -> b -> [a] -> [b]
scanr' f q0 []     =  [q0]
scanr' f q0 (x:xs) = let qs = scanr' f q0 xs 
    in f x (head' qs) : qs
--                     where qs@(q:_) = scanr f q0 xs 

scanr1'          :: (a -> a -> a) -> [a] -> [a]
scanr1' f []     =  []
scanr1' f [x]    =  [x]
scanr1' f (x:xs) =  let qs = scanr1' f xs
    in f x (head' qs) : qs

-- iterate f x returns an infinite list of repeated applications of f to x:
-- iterate f x == [x, f x, f (f x), ...]

iterate'          :: (a -> a) -> a -> [a]
iterate' f x      =  x : iterate' f (f x)

-- repeat x is an infinite list, with x the value of every element.

repeat'           :: a -> [a]
repeat' x         =  x: (repeat' x)

-- replicate n x is a list of length n with x the value of every element

replicate'        :: Int -> a -> [a]
replicate' n x    =  take' n (repeat' x)

-- cycle ties a finite list into a circular one, or equivalently,
-- the infinite repetition of the original list.  It is the identity
-- on infinite lists.

cycle'            :: [a] -> [a]
cycle' []         =  error "Prelude.cycle: empty list"
cycle' xs         =  xs ++# cycle' xs
-- cycle xs         =  xs' where xs' = xs ++ xs'

-- take n, applied to a list xs, returns the prefix of xs of length n,
-- or xs itself if n > length xs.  drop n xs returns the suffix of xs
-- after the first n elements, or [] if n > length xs.  splitAt n xs
-- is equivalent to (take n xs, drop n xs).

take'                   :: Int -> [a] -> [a]
take' n _      | n <= 0 =  []
take' _ []              =  []
take' n (x:xs)          =  x : take' (n - 1) xs

drop'                   :: Int -> [a] -> [a]
drop' n xs     | n <= 0 =  xs
drop' _ []              =  []
drop' n (_:xs)          =  drop' (n - 1) xs

splitAt'                  :: Int -> [a] -> ([a],[a])
splitAt' n xs             =  (take' n xs, drop' n xs)

-- takeWhile, applied to a predicate p and a list xs, returns the longest
-- prefix (possibly empty) of xs of elements that satisfy p.  dropWhile p xs
-- returns the remaining suffix.  span p xs is equivalent to 
-- (takeWhile p xs, dropWhile p xs), while break p uses the negation of p.

takeWhile'               :: (a -> Bool) -> [a] -> [a]
takeWhile' p []          =  []
takeWhile' p (x:xs) 
            | p x        =  x : takeWhile' p xs
            | otherwise' =  []

dropWhile'               :: (a -> Bool) -> [a] -> [a]
dropWhile' p []          =  []
dropWhile' p (x:xs)
            | p x       =  dropWhile' p xs
            | otherwise' =  x:xs

span', break'             :: (a -> Bool) -> [a] -> ([a],[a])
span' p []               = ([],[])
span' p (x:xs) 
            | p x = let yz = span' p xs
                 in (x:(fst yz), snd yz) 
            | otherwise' =  ([],x:xs)
--            | p x       =  (x:ys,zs) 
--                           where (ys,zs) = span p xs

break' p                 =  span' (not . p)

-- lines breaks a string up into a list of strings at newline characters.
-- The resulting strings do not contain newlines.  Similary, words
-- breaks a string up into a list of words, which were delimited by
-- white space.  unlines and unwords are the inverse operations.
-- unlines joins lines with terminating newlines, and unwords joins
-- words with separating spaces.

-- isSpace' :: Char -> Bool
-- isSpace' c =  elem' c " \t\n\r\f\v\xA0"
 
lines'            :: String -> [String]
lines' s = if s == "" then []
           else let ls = break' (== '\n') s
                    l = fst ls
                    s' = snd ls
                  in  l : case s' of
                                []      -> []
                                (_:s'') -> lines' s''

{-
words'            :: String -> [String]
words' s          =  let s' = dropWhile' isSpace' s 
                     in if s' == "" then []
                        else let ws = break' isSpace' s'
                             in (fst ws) : words' (snd ws)
-}

-- unlines'          :: [String] -> String
-- unlines'          =  concatMap' (++# "\n")

{-
unwords'          :: [String] -> String
unwords' []       =  ""
unwords' ws       =  foldr1' (\w s -> w ++# (' ':s)) ws
-}

-- reverse xs returns the elements of xs in reverse order.  xs must be finite.

reverse'          :: [a] -> [a]
reverse'          =  foldl' (flip (:)) []

-- and returns the conjunction of a Boolean list.  For the result to be
-- True, the list must be finite; False, however, results from a False
-- value at a finite index of a finite or infinite list.  or is the
-- disjunctive dual of and.

and', or'          :: [Bool] -> Bool
and'              =  foldr' (&&) True
or'               =  foldr' (||) False

-- Applied to a predicate and a list, any determines if any element
-- of the list satisfies the predicate.  Similarly, for all.

any', all'         :: (a -> Bool) -> [a] -> Bool
any' p            =  or' . map p
all' p            =  and' . map p

-- elem is the list membership predicate, usually written in infix form,
-- e.g., x `elem` xs.  notElem is the negation.

elem', notElem'    :: (Eq a) => a -> [a] -> Bool
elem' x           =  any' (== x)
notElem' x        =  all' (/= x)

-- lookup key assocs looks up a key in an association list.

lookup'           :: (Eq a) => a -> [(a,b)] -> Maybe b
lookup' key []    =  Nothing
lookup' key (xy : xys)
    | key == fst xy   =  Just (snd xy)
    | otherwise'       =  lookup' key xys

-- sum and product compute the sum or product of a finite list of numbers.

sum', product'     :: (Num a) => [a] -> a
sum'              =  foldl' (+) 0  
product'          =  foldl' (*) 1

-- maximum and minimum return the maximum or minimum value from a list,
-- which must be non-empty, finite, and of an ordered type.

{-
maximum', minimum' :: (Ord a) => [a] -> a
maximum' []       =  error "Prelude.maximum: empty list"
maximum' xs       =  foldl1' max xs

minimum' []       =  error "Prelude.minimum: empty list"
minimum' xs       =  foldl1' min xs
-}

-- zip takes two lists and returns a list of corresponding pairs.  If one
-- input list is short, excess elements of the longer list are discarded.
-- zip3 takes three lists and returns a list of triples.  Zips for larger
-- tuples are in the List library

zip'              :: [a] -> [b] -> [(a,b)]
zip'              =  zipWith' (,)

-- The zipWith family generalises the zip family by zipping with the
-- function given as the first argument, instead of a tupling function.
-- For example, zipWith (+) is applied to two lists to produce the list
-- of corresponding sums.

zipWith'          :: (a->b->c) -> [a]->[b]->[c]
zipWith' z (a:as) (b:bs)
                 =  z a b : zipWith' z as bs
zipWith' _ _ _    =  []

-- unzip transforms a list of pairs into a pair of lists.  
unzip'            :: [(a,b)] -> ([a],[b])
unzip'            =  foldr' (\x xs -> ((fst x):
                               (fst xs),(snd x):(snd xs))) ([],[])

