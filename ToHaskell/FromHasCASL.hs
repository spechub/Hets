{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

   
   The comorphism functions for HasCASL2Haskell
-}

module ToHaskell.FromHasCASL where

import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Result
import qualified Common.Lib.Map as Map 

import HasCASL.Le

import ParseMonad
import LexerOptions
import PropLexer
import PropParser as HsParser
import PNT
import PropPosSyntax hiding (ModuleName, Id, HsName)
import qualified NewPrettyPrint as HatPretty

import Haskell.HatAna
import Haskell.HatParser

import ToHaskell.TranslateAna
import Data.List ((\\))

mapSingleSentence :: Env -> Sentence -> Maybe (HsDeclI PNT)
mapSingleSentence sign sen = 
    case mapTheory $ moveDataEntries (sign, [NamedSen "" sen]) of 
    Nothing -> Nothing
    Just (_, l) -> case l of 
      [] -> Nothing
      [s] -> Just $ sentence s
      _ -> case mapTheory (sign, []) of
           Nothing -> Nothing
           Just (_, o) -> case l \\ o of
             [] -> Nothing
             [s] -> Just $ sentence s
             _ -> Nothing

moveDataEntries :: (Env, [Named Sentence]) -> (Env, [Named Sentence])
moveDataEntries (e, l) = case l of 
  [] -> (e, l)
  NamedSen n (DatatypeSen s) : r -> case s of
     [] -> moveDataEntries (e, r)
     d@(DataEntry im i _ _ _) : t -> let 
       j = Map.findWithDefault i i im 
       tm = typeMap e
       m = Map.lookup j tm in
       case m of 
        Nothing -> error "moveDataEntries"
        Just ti -> moveDataEntries (e { typeMap = Map.insert j 
                                  ti { typeDefn = DatatypeDefn d } tm },
                    NamedSen n (DatatypeSen t) : r)
  s : r -> let (e2, r2) = moveDataEntries (e , r) in (e2, s : r2)

mapTheory :: (Env, [Named Sentence]) -> Maybe (Sign, [Named (HsDeclI PNT)])
mapTheory (sig, csens) =
    let hs = translateSig sig
	ps = concatMap (translateSentence sig) csens
	cs = cleanSig hs ps
        res@(Result _ m) = 
            hatAna (HsDecls (preludeDecls ++ cs ++ map sentence ps),
                            emptySign, emptyGlobalAnnos)
    in case m of 
    Nothing -> error $ show res
    Just (_, _, hsig, sens) -> Just (diffSign hsig preludeSign, 
                  filter noInstance sens \\ preludeSens) 

noInstance :: Named (HsDeclI PNT) -> Bool
noInstance s = case basestruct $ struct $ sentence s of
               Just (HsInstDecl _ _ _ _ _) -> False
               Just (HsFunBind _ ms) -> all (\ m -> case m of
                     HsMatch _ n _ _ _ ->  let i = HatPretty.pp n in
                           take 3 i /= "$--" && 
                           take 9 i /= "default__" && 
                           i /= "shows" && 
                           i /= "showArgument") ms
               _ -> True

preludeSign :: Sign
preludeSign = fst preludeTheory

preludeSens :: [Named (HsDeclI PNT)]
preludeSens = snd preludeTheory

preludeTheory :: (Sign, [Named (HsDeclI PNT)])
preludeTheory = case maybeResult $ hatAna 
                (HsDecls preludeDecls, emptySign, emptyGlobalAnnos) of
                Just (_, _, hs, sens) -> (hs, sens) 
                _ -> error "preludeTheory"

preludeDecls :: [HsDecl]
preludeDecls = let ts = pLexerPass0 lexerflags0 
                        -- adjust line number of module Prelude by hand!
                        (replicate 113 '\n' ++ preludeString)
   in case parseTokens (HsParser.parse) "ToHaskell/FromHasCASL.hs" ts of
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
 \type Unit = Bool\n\
 \type Pred a = a -> Bool\n\
 \\n\
 \bottom :: a\n\
 \bottom = error \"bottom\"\n\
 \\n\
 \a___2_S_B_2 :: (Bool, Bool) -> Bool\n\
 \a___2_S_B_2 = bottom\n\
 \ \n\
 \a___2_L_E_G_2 :: (Bool, Bool) -> Bool\n\
 \a___2_L_E_G_2 = bottom\n\
 \ \n\
 \a___2_E_2 :: (a, a) -> Bool\n\
 \a___2_E_2 = bottom\n\
 \ \n\
 \a___2_E_G_2 :: (Bool, Bool) -> Bool\n\
 \a___2_E_G_2 (a, b) = if a then b else True\n\
 \ \n\
 \a___2_Ee_E_2 :: (a, a) -> Bool\n\
 \a___2_Ee_E_2 = bottom\n\
 \ \n\
 \a___2_B_S_2 :: (Bool, Bool) -> Bool\n\
 \a___2_B_S_2 = bottom\n\
 \\n\
 \a___2if_2 :: (Bool, Bool) -> Bool\n\
 \a___2if_2 (a, b) = if b then a else True\n\
 \\n\
 \a___2when_2else_2 :: (a, Bool, a) -> a\n\
 \a___2when_2else_2 (a, b, c) = if b then a else c \n\
 \\n\
 \not_2 :: Bool -> Bool\n\
 \not_2 = bottom\n\
 \\n\
 \def_2 :: a -> Bool\n\
 \def_2 a = bottom\n\
 \ \n\
 \false :: Bool\n\
 \false = False\n\
 \\n\
 \true :: Bool\n\
 \true = True"
