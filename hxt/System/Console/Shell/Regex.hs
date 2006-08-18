{-# OPTIONS -cpp #-}
{-
 - 
 -  Copyright 2005-2006, Robert Dockins.
 -  
 -}

{-   This module implements a pretty hokey version of regular expressions.
 -   They are used to parse the arguments to shell commands and to give
 -   information about the type of the argument at a position in the
 -   string to allow positional word completion.  The REs are directly
 -   intertreted in the list monad, so effeciency isn't so great, but
 -   for most shell command lines that won't matter too much.
 -}

module System.Console.Shell.Regex where

import Numeric               ( readDec, readFloat, readHex )
import Control.Monad         ( MonadPlus(..) )


{-  The type of regular expressions.  Regular expressions evaluation
    calculates a result value as well as recognizing strings in a language,
    so we use a GADT which follows the structure of the evaluation.
-}

-- hide GADTs from haddock
#ifndef __HADDOCK__

data Regex a x where
  Empty     :: Regex a x
  Epsilon   :: x -> Regex a x
  Label     :: String -> Regex a x -> Regex a x
  Terminal  :: (a -> Bool) -> (a -> x) -> String -> Regex a x
  External  :: ([a] -> [(x,[a])]) -> String -> Regex a x

  Concat    :: (p -> q -> x)           -> Regex a p -> Regex a q -> Regex a x
  Alt       :: (Either p q -> x)       -> Regex a p -> Regex a q -> Regex a x
  Star      :: ([p] -> x)              -> Regex a p -> Regex a x

#endif

{-  Auxiliary type used to help remove unnecessary parenthesis when printing REs -}
data RegexContext
  = TopContext
  | AltContext
  | ConcatContext
  | StarContext
 deriving Eq

{-  Print a string representation of a regular expression.
    Really only useful for debugging becuase there is no
    inverse (parser).
-}
showRegex :: RegexContext -> Regex a x -> String
showRegex cxt (Label l _)      = l
showRegex cxt Empty            = "%empty"
showRegex cxt (Epsilon _)      = ""
showRegex cxt (Terminal _ _ l) = l
showRegex cxt (External _ l)   = l
showRegex cxt (Alt _ p q)      = parenIf (cxt == StarContext || cxt == ConcatContext) $
                                  concat [showRegex AltContext p,"|",showRegex AltContext q]
showRegex cxt (Concat _ p q)   = parenIf (cxt == StarContext) $
                                  concat [showRegex ConcatContext p,showRegex ConcatContext q]
showRegex cxt (Star _ x)       = concat [showRegex StarContext x,"*"]

parenIf :: Bool -> String -> String
parenIf False str = str
parenIf True str = "("++str++")"

instance Show (Regex a x) where
  show = showRegex TopContext


{- Returns true if the regular expressions matches the 
   input list -}
matchesRegex :: Regex a x -> [a] -> Bool
matchesRegex re ts = not (null (matchRegex re ts))

{- Generates a list of all calculated values from 
   matches on the RE.  Returns the empty list if
   there are no matches 
-}
matchRegex :: Regex a x -> [a] -> [x]
matchRegex re ts = [ x | (x,[]) <- runRegex re ts ]

{- Generates a list corresponding to all
   partial matches of the regular expression.
   The first component is the calculated value and
   the second component is the remaining unmatched input
-}
runRegex :: Regex a x -> [a] -> [(x,[a])]

runRegex Empty ts = mzero

runRegex (Epsilon x) ts = return (x,ts)

runRegex (Terminal cond f _) (t:ts)
   | cond t    = return (f t,ts)
   | otherwise = mzero

runRegex (Label _ re) ts = runRegex re ts

runRegex (Concat f p q) ts =
   do (a,ts')  <- runRegex p ts
      (b,ts'') <- runRegex q ts'
      return (f a b,ts'')

runRegex (Alt f p q) ts =
     (runRegex p ts >>= \(a,ts') -> return (f (Left a),ts')) `mplus`
     (runRegex q ts >>= \(a,ts') -> return (f (Right a),ts'))

runRegex (Star f p) ts = match [] ts
  where match as ts =
          (runRegex p ts >>= \(a,ts') -> match (a:as) ts') `mplus`
          (return (f (reverse as),ts))

runRegex (External f _) ts = f ts

runRegex _ _ = mzero


strEpsilon :: Regex Char String
strEpsilon     = Epsilon []
strTerminal ch = Terminal (==ch) (:[]) [ch]
strConcat      = Concat (++)
strAlt         = altProj
strStar        = Star concat
strSpace       = Terminal (`elem` " \v\t\n\r\f") id ""
strAny         = Terminal (const True) (:[]) ""

altProj = Alt (\x -> case x of Left a -> a; Right a -> a)

starRegex :: Regex a x -> Regex a [x]
starRegex re = Star id re

plusRegex :: Regex a x -> Regex a [x]
plusRegex re = Label (concat [showRegex TopContext re,"+"]) $
    Concat (:) re (Star id re)

optRegex :: Regex a x -> Regex a (Maybe x)
optRegex re = Label (concat ["[",showRegex TopContext re,"]"]) $
    Alt (\x -> case x of Left a -> Just a; Right () -> Nothing)
      re
      (Epsilon ())

manyRegex :: Regex a x -> Regex a y ->  Regex a [x]
manyRegex re sep = Label (concat ["{",showRegex TopContext re,"}"]) $
    (Concat (:) re (Star id (Concat (\_ x -> x) sep re)))
      `altProj` (Epsilon [] )

stringRegex :: String -> x -> Regex Char x
stringRegex str v = foldr (\c -> Concat (\_ x -> x) (strTerminal c)) (Epsilon v) str

anyOfRegex :: [(String,x)] -> Regex Char x
anyOfRegex [] = Empty
anyOfRegex xs = foldr1 altProj (map (uncurry stringRegex) xs)

spaceRegex :: Regex Char String
spaceRegex = Label " " (plusRegex strSpace)

maybeSpaceRegex :: Regex Char String
maybeSpaceRegex = Label "" (starRegex strSpace)

maybeSpaceBefore :: Regex Char x -> Regex Char x
maybeSpaceBefore re = Concat (\_ x -> x) maybeSpaceRegex re

spaceAfter :: Regex Char x -> Regex Char x
spaceAfter re = Concat (\x _ -> x) re spaceRegex

maybeSpaceAfter :: Regex Char x -> Regex Char x
maybeSpaceAfter re = Concat (\x _ -> x) re maybeSpaceRegex

signRegex :: Num a => Regex Char (a -> a)
signRegex =
    (Epsilon id) `altProj`
    (Terminal (== '+') (const id) "+") `altProj`
    (Terminal (== '-') (const negate) "-")

intRegex :: Integral a => Regex Char a
intRegex = Label "<integer>" $
    Concat (\sign int -> sign int) signRegex (External readDec "")

floatRegex :: RealFloat a => Regex Char a
floatRegex = Label "<float>" $
    Concat (\sign float -> sign float) signRegex (External readFloat "")

boolRegex :: Regex Char Bool
boolRegex = Label "<boolean>" $
   stringRegex "true"  True  `altProj`
   stringRegex "false" False `altProj`
   stringRegex "yes"   True  `altProj`
   stringRegex "no"    False `altProj`
   stringRegex "t"     True  `altProj`
   stringRegex "f"     False `altProj`
   stringRegex "y"     True  `altProj`
   stringRegex "n"     False `altProj`
   stringRegex "1"     True  `altProj`
   stringRegex "0"     False

wordsRegex :: String -> Regex Char [String]
wordsRegex wbc = manyRegex (wordRegex wbc) spaceRegex

wordRegex :: String -> Regex Char String
wordRegex wbc = Label "<word>" $
     plusRegex wordChar `altProj`
     singleQuotes `altProj`
     doubleQuotes

  where
     wordChar = Terminal (not . (`elem` wbc)) id ""

     singleQuotes =
       Concat (\_ x -> x) (strTerminal '\'')  $
       Concat (\x _ -> x) (Star id (Terminal (/= '\'') id "")) $
                          (strTerminal '\'')

     doubleQuotes =
       Concat (\_ x -> x) (strTerminal '\"') $
       Concat (\x _ -> x) (Star id insideDQuotes) $
                          (strTerminal '\"')

     insideDQuotes =
       (Terminal (not . (`elem` "\\\"")) id "") `altProj`
       (Concat (\_ x -> x)
          (strTerminal '\\')
          escapes
       )

     escapes =
       Alt (\x -> case x of Left a -> a; Right i -> toEnum i)
        ( (Terminal (== 'a')  (const '\a') "") `altProj`
          (Terminal (== 'b')  (const '\b') "") `altProj`
          (Terminal (== 'f')  (const '\f') "") `altProj`
          (Terminal (== 'n')  (const '\n') "") `altProj`
          (Terminal (== 'r')  (const '\r') "") `altProj`
          (Terminal (== 't')  (const '\t') "") `altProj`
          (Terminal (== 'v')  (const '\v') "") `altProj`
          (Terminal (== '\\') (const '\\') "") `altProj`
          (Terminal (== '\'') (const '\'') "")
        )
        ( ( Concat (\_ x -> x) (strTerminal '0') $
            Concat (\_ x -> x) (strTerminal 'x') $
            External readHex ""
          ) `altProj`
          ( Concat (\_ x -> x) (strTerminal 'x') $
            External readHex ""
          ) `altProj`
          ( External readDec ""
          )
        )
