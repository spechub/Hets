{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  non-portable 
   
test the programatica parser and (HatAna) analysis

-}

module Main where

import Haskell.HatParser
import Haskell.HatAna
import ParseMonad
import LexerOptions
import PropLexer
import PropParser as HP
import PropPosSyntax

import System.Environment

import Common.Result
import Common.AnnoState
import Common.AS_Annotation
import Common.Print_AS_Annotation()
import Common.GlobalAnnotations
import Common.PrettyPrint

hParser :: AParser () (Sign, [Named (HsDeclI PNT)])
hParser = do 
   b <- hatParser
   let res@(Result _ m) = hatAna(b, emptySign, emptyGlobalAnnos)
   case m of 
      Nothing -> error $ show res
      Just (_, _, sig, sens) -> return (sig, sens)

main :: IO ()
main = do l <- getArgs
	  if length l >= 1 then
	     do let fn = head l 
                s <- readFile fn
                let ts = pLexerPass0 lexerflags0 s
                    Result ds m = do 
                      HsModule _ _ _ _ b <- parseTokens HP.parse fn ts
                      hatAna(HsDecls (preludeDecls ++ b), 
                                     emptySign, emptyGlobalAnnos) 
	        case m of 
		       Just (_, _, sig, hs) -> do
		           putStrLn $ showPretty sig ""
			   mapM_ (putStrLn . flip showPretty "") hs
		       _ -> mapM_ (putStrLn . show) ds
	     else putStrLn "missing argument"

preludeDecls :: [HsDecl]
preludeDecls = let ts = pLexerPass0 lexerflags0 
                        -- adjust line number of 'preludeString =' by hand!
                        (replicate 28 '\n' ++ preludeString)
   in case parseTokens (HP.parse) "Haskell/hana.hs" ts of
      Just (HsModule _ _ _ _ ds) -> ds
      _ -> error "preludeDecls"

preludeString :: String
preludeString =
 "module Prelude where\n\
 \data Integer\n\
 \data Rational\n\
 \data Double\n\
 \data Char\n\
 \data Int\n\
 \\n\
 \data (->) a b\n\
 \\n\
 \data Bool = False | True deriving (Show, Eq, Ord)\n\
 \\n\
 \not              :: Bool -> Bool\n\
 \not True         =  False\n\
 \not False        =  True\n\
 \\n\
 \otherwise = True\n\
 \\n\
 \(&&) :: Bool -> Bool -> Bool\n\
 \a && b = if a then True else b\n\
 \\n\
 \data  Ordering  =  LT | EQ | GT\n\
 \          deriving (Show, Eq, Ord)\n\
 \\n\
 \lexOrder EQ o = o\n\
 \lexOrder o  _ = o\n\
 \\n\
 \class  Eq a  where\n\
 \    (==), (/=)       :: a -> a -> Bool\n\
 \\n\
 \    x /= y           =  not (x == y)\n\
 \    x == y           =  not (x /= y)\n\
 \\n\
 \data [a] = [] | (:) { head :: a , tail :: [a] } deriving (Show, Eq, Ord)\n\
 \(++) :: [a] -> [a] -> [a]\n\
 \\n\
 \[]     ++ ys = ys\n\
 \(x:xs) ++ ys = x : (xs ++ ys)\n\
 \\n\
 \type  String = [Char]\n\
 \\n\
 \foreign import primError       :: String -> a\n\
 \\n\
 \error            :: String -> a\n\
 \error = primError\n\
 \\n\
 \(.)              :: (b -> c) -> (a -> b) -> a -> c\n\
 \f . g            =  \\ x -> f (g x)\n\
 \\n\
 \type  ShowS    = String -> String\n\
 \\n\
 \class  (Eq a) => Ord a  where\n\
 \    compare              :: a -> a -> Ordering\n\
 \    (<), (<=), (>=), (>) :: a -> a -> Bool\n\
 \    max, min             :: a -> a -> a\n\
 \\n\
 \        -- Minimal complete definition:\n\
 \        --      (<=) or compare\n\
 \        -- Using compare can be more efficient for complex types.\n\
 \    compare x y\n\
 \         | x == y    =  EQ\n\
 \         | x <= y    =  LT\n\
 \         | otherwise =  GT\n\
 \\n\
 \    x <= y           =  compare x y /= GT\n\
 \    x <  y           =  compare x y == LT\n\
 \    x >= y           =  compare x y /= LT\n\
 \    x >  y           =  compare x y == GT\n\
 \\n\
 \-- note that (min x y, max x y) = (x,y) or (y,x)\n\
 \    max x y\n\
 \         | x <= y    =  y\n\
 \         | otherwise =  x\n\
 \    min x y\n\
 \         | x <= y    =  x\n\
 \         | otherwise =  y\n\
 \\n\
 \shows            :: (Show a) => a -> ShowS\n\
 \shows            =  showsPrec 0\n\
 \\n\
 \showChar         :: Char -> ShowS\n\
 \showChar         =  (:)\n\
 \\n\
 \showString       :: String -> ShowS\n\
 \showString       =  (++)\n\
 \\n\
 \showParen        :: Bool -> ShowS -> ShowS\n\
 \showParen b p    =  if b then showChar '(' . p . showChar ')' else p\n\
 \\n\
 \-- Basic printing combinators (nonstd, for use in derived Show instances):\n\
 \\n\
 \showParenArg :: Int -> ShowS -> ShowS\n\
 \showParenArg d = showParen (10<=d)\n\
 \\n\
 \showArgument x = showChar ' ' . showsPrec 10 x\n\
 \\n\
 \class  Show a  where\n\
 \    showsPrec        :: Int -> a -> ShowS\n\
 \    show             :: a -> String\n\
 \    showList         :: [a] -> ShowS\n\
 \\n\
 \    showsPrec _ x s   = show x ++ s\n\
 \\n\
 \    show x        = showsPrec 0 x \"\"\n\
 \\n\
 \    showList []       = showString \"[]\"\n\
 \    showList (x:xs)   = showChar '[' . shows x . showl xs\n\
 \                        where showl []     = showChar ']'\n\
 \                              showl (x:xs) = showChar ',' . shows x .\n\
 \                                             showl xs\n\
 \\n\
 \\n\
 \class  (Eq a, Show a) => Num a  where\n\
 \    (+), (-), (*)    :: a -> a -> a\n\
 \    negate           :: a -> a\n\
 \    abs, signum      :: a -> a\n\
 \    fromInteger      :: Integer -> a\n\
 \\n\
 \class  (Num a) => Fractional a  where\n\
 \    (/)              :: a -> a -> a\n\
 \    recip            :: a -> a\n\
 \    fromRational     :: Rational -> a\n\
 \\n\
 \instance Num Int\n\
 \instance Num Integer\n\
 \instance Num Rational\n\
 \instance Num Double\n\
 \instance Eq Int\n\
 \instance Ord Int\n\
 \instance Eq Char\n\
 \instance Eq Integer\n\
 \instance Eq Rational\n\
 \instance Eq Double\n\
 \instance Ord Char\n\
 \instance Ord Integer\n\
 \instance Ord Rational\n\
 \instance Ord Double\n\
 \instance Show Int\n\
 \instance Show Char\n\
 \instance Show Integer\n\
 \instance Show Rational\n\
 \instance Show Double\n\
 \instance Fractional Rational\n\
 \instance Fractional Double\n\
 \\n\
 \data  ()  =  () deriving (Eq, Ord, Show)\n\
 \\n\
 \data  (a,b)\n\
 \   =  (,) a b\n\
 \   deriving (Show, Eq, Ord)\n\
 \\n\
 \data  (a,b,c)\n\
 \   =  (,,) a b c\n\
 \   deriving (Show, Eq, Ord)\n\
 \\n\
 \data  (a,b,c, d)\n\
 \   =  (,,,) a b c d\n\
 \   deriving (Show, Eq, Ord)\n\
 \last             :: [a] -> a\n\
 \last [x]         =  x\n\
 \last (_:xs)      =  last xs\n\
 \last []          =  error \"Prelude.last: empty list\""
