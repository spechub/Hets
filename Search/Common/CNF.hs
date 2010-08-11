{- |
Module      :  $Header$
Description :  Translation to conjunctive normal form
Copyright   :  (c) Immanuel Normann, Uni Bremen 2007
License     :  GPLv2 or higher

Maintainer  :  inormann@jacobs-university.de
Stability   :  provisional
Portability :  portable
-}
module Search.CNF where

import Search.Utils.List -- fuer mapShow
import Data.List

data Term = T Connective [Term] | V Int
data Connective = And | Or | Not deriving (Eq,Show)

instance Show (Term) where
    show (T c args) = "(" ++ show c ++ " " ++ (mapShow " " args) ++ ")"
    show (V n) = show n

stripOff :: [Term] -> [Term]
stripOff ((T _ fs1):fs2) = fs1 ++ (stripOff fs2)
stripOff (f:fs2) = f:(stripOff fs2)
stripOff [] = []

isC :: Connective -> Term -> Bool
isC c (T a _) = c == a
isC _ _ = False

makeOrAndTree :: Term -> Term
makeOrAndTree (T And ts) = (T And (ands ++ others))
    where (ands',others) = partition (isC And) ts
          ands = stripOff ands'
makeOrAndTree (T Or ts) = (T Or (ands ++ ors ++ nots))
    where (ands,others) = partition (isC And) ts
          (ors',nots) = partition (isC Or) others
          ors = stripOff ors'
makeOrAndTree f = f          

isLiteral :: Term -> Bool
isLiteral (V _) = True
isLiteral (T Not [V _]) = True
isLiteral _ = False

isClause :: Term -> Bool
isClause (T Or ts) = all isLiteral ts
isClause t = isLiteral t

isCNF :: Term -> Bool
isCNF (T And ts) = all isClause ts
isCNF t = isClause t


distOr :: Term -> [Term]
distOr (T Or ((T And (f:fs1)):fs2)) = 
    (T Or (f:fs2)):(distOr (T Or ((T And fs1):fs2)))
distOr (T Or ((T And []):fs2)) = []
distOr f = [f]

data TermType = CNF | OrAndTree | OtherTree deriving Show

termType :: Term -> TermType
termType (T Or ((T And _):_)) = OrAndTree
termType t = if (isCNF t) then CNF else OtherTree

cnf t = case (termType t)
        of CNF -> t
           OrAndTree -> cnf (T And (distOr t))
           OtherTree -> cnf $ makeOrAndTree $ cnfChildren t
               where cnfChildren (T c ts) = (T c (map cnf ts))
                     cnfChildren t = t

f1 = T And [V 1,T And [V 2,V 3],V 4,T Or [V 5,V 6],T And [V 7,V 8],T Not [V 9]]
f2 = T Or [T And [V 1,T And [V 2,V 3]],V 4]
f3 = T Or [T Or [T Not [V 1],V 2,T And [V 3,V 4]],T Or [T And [T And [V 5,V 6],T Or [V 7,V 9]]]]

tt = termType
ft = makeOrAndTree