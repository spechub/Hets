{- |
Module      :  $Header$
Description :  Dealing with transformation from/to Haskell and Maude
Copyright   :  (c) Adrian Riesco, Facultad de Informatica UCM 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  ariesco@fdi.ucm.es
Stability   :  experimental
Portability :  portable

Translations between Maude and Haskell
-}
{-
  Ref.

  ...
-}

module Maude.Printing where

import Maude.AS_Maude
import Maude.Sign

import qualified Data.Set as Set
import qualified Common.Lib.Rel as Rel

import Common.Id (Token)

getSpec :: [Char] -> [Char]
getSpec =  quitNil . quitEnd . quitBegin

quitBegin :: [Char] -> [Char]
quitBegin ('S' : ('p' : l))  = 'S' : ('p' : l)
quitBegin (_ : l) = quitBegin l
quitBegin [] = []

quitEnd :: [Char] -> [Char]
quitEnd ('M' : ('a' : ('u' : _))) = []
quitEnd (h : l) = h : (quitEnd l)
quitEnd [] = []

quitNil :: [Char] -> [Char]
quitNil = Prelude.filter (/= '\NUL')

sign2maude :: Sign -> [Char]
sign2maude sign = "(fmod A is " ++ ss ++ sbs ++ opd ++ " endfm)"
 where ss = sorts2maude (sorts sign)
       sbs = subsorts2maude (subsorts sign)
       opd = ops2maude (ops sign)

sorts2maude :: SortSet -> [Char]
sorts2maude ss = if Set.null ss
                    then ""
                    else "sorts " ++ Set.fold (++) "" (Set.map ((++ " ") . show) ss) ++ ". "

subsorts2maude :: SubsortRel -> [Char]
subsorts2maude ssbs = if Rel.null ssbs
                         then ""
                         else foldr (++) "" (map printPair (Rel.toList ssbs))

printPair :: (Token,Token) -> [Char]
printPair (a,b) = "subsort " ++ show a ++ " < " ++ show b ++ " . "

ops2maude :: OpMap -> [Char]
ops2maude ops = []