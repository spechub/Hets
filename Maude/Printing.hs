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

import qualified Data.Set as Set
import qualified Data.Map  as Map
import qualified Common.Lib.Rel as Rel

import Common.Id (Token)

getSpec :: String -> String
getSpec =  quitNil . quitEnd . quitBegin

quitBegin :: String -> String
quitBegin ('S' : ('p' : l))  = 'S' : ('p' : l)
quitBegin (_ : l) = quitBegin l
quitBegin [] = []

quitEnd :: String -> String
quitEnd ('@' : ('#' : ('$' : ('e' : ('n' : _))))) = []
quitEnd (h : l) = h : (quitEnd l)
quitEnd [] = []

quitNil :: String -> String
quitNil = Prelude.filter (/= '\NUL')

printSign :: Set.Set Qid -> Rel.Rel Qid
             -> Map.Map Qid (Set.Set ([Qid], Qid, [Attr])) -> String
printSign sts sbsts ops = ss ++ sbs ++ opd
 where ss = sorts2maude sts
       sbs = subsorts2maude sbsts
       opd = ops2maude ops

sorts2maude :: Set.Set Qid -> String
sorts2maude ss = if Set.null ss
                    then ""
                    else "sorts " ++ Set.fold (++) "" (Set.map ((++ " ") . show) ss) ++ ".\n"

subsorts2maude :: Rel.Rel Qid -> String
subsorts2maude ssbs = if Rel.null ssbs
                         then ""
                         else foldr (++) "" (map printPair $ Rel.toList ssbs)

printPair :: (Token,Token) -> String
printPair (a,b) = "subsort " ++ show a ++ " < " ++ show b ++ " .\n"

ops2maude :: Map.Map Qid (Set.Set ([Qid], Qid, [Attr])) -> String
ops2maude om = flatten (flatten (map printOp (Map.toList om)))

flatten :: [[a]] -> [a]
flatten [] = []
flatten (a : l) = a ++ (flatten l)

printOp :: (Qid, Set.Set ([Qid], Qid, [Attr])) -> [String]
printOp (opid, s) = map (printOpAux opid) (Set.toList s)

printOpAux :: Qid -> ([Qid], Qid, [Attr]) -> String
printOpAux opid (ar, co, ats) = "op " ++ show opid ++ " : " ++ printArity ar ++
                                " -> " ++ show co ++ printAttrSet ats ++ " .\n"

printArity :: [Qid] -> String
printArity a = foldr (++) "" (map showSpace a)

showSpace ::Show t => t -> String
showSpace s = show s ++ " "

printAttrSet :: [Attr] -> String
printAttrSet [] = []
printAttrSet ats = " [" ++ printAttrSetAux ats ++ "] " 

printAttrSetAux :: [Attr] -> String
printAttrSetAux [] = []
printAttrSetAux [a] = printAttr a
printAttrSetAux (a : ats) = printAttr a ++ " " ++ printAttrSetAux ats

printAttr :: Attr -> String
printAttr Comm = "comm"
printAttr Assoc = "assoc"
printAttr Idem = "idem"
printAttr Iter = "iter"
printAttr Memo = "memo"
printAttr Ctor = "ctor"
printAttr Msg = "msg"
printAttr Object = "object"
printAttr (Id t) = "id: " ++ printTerm t
printAttr (LeftId t) = "id-left: " ++ printTerm t
printAttr (RightId t) = "id-right: " ++ printTerm t
printAttr (Prec p) = "prec " ++ show p
printAttr (Strat ls) = "strat (" ++ printListSpaces ls ++ ")"
printAttr (Poly ls) = "poly (" ++ printListSpaces ls ++ ")"
printAttr (Frozen ls) = if null ls
                           then "frozen"
                           else "frozen (" ++ printListSpaces ls ++ ")"
printAttr (Gather ls) = "gather (" ++ printListSpaces ls ++ ")"
printAttr (Format ls) = "format (" ++ printListSpaces ls ++ ")"
printAttr _ = ""

printStmntAttrSet :: [StmntAttr] -> String
printStmntAttrSet [] = []
printStmntAttrSet ats = " [ " ++ printStmntAttrSetAux ats ++ " ] " 

printStmntAttrSetAux :: [StmntAttr] -> String
printStmntAttrSetAux [] = []
printStmntAttrSetAux [a] = printAttrStmnt a
printStmntAttrSetAux (a : ats) = printAttrStmnt a ++ " " ++ printStmntAttrSetAux ats

printAttrStmnt :: StmntAttr -> String
printAttrStmnt Owise = "owise"
printAttrStmnt Nonexec = "nonexec"
printAttrStmnt (Metadata s) = "metadata \"" ++ s ++ "\""
printAttrStmnt (Label q) = "label \"" ++ show q ++ "\""
printAttrStmnt (Print _) = ""

printTerm :: Term -> String
printTerm (Const q _) = show q
printTerm (Var q _) = show q
printTerm (Apply q tl) = show q ++ "(" ++ printTermList tl ++ ")"

printTermList :: [Term] -> String
printTermList [] = []
printTermList [t] = printTerm t
printTermList (t : tl) = printTerm t ++ ", " ++ printTermList tl

printListSpaces :: Show t => [t] -> String
printListSpaces = foldr ((++) . showSpace) ""

printMb :: Membership -> String
printMb (Mb t s conds ats) = "mb " ++ printTerm t ++ " : " ++ printSort s ++
                             printConds conds ++ printStmntAttrSet ats ++ " .\n"

printEq :: Equation -> String
printEq (Eq t1 t2 conds ats) = "eq " ++ printTerm t1 ++ " = " ++ printTerm t2 ++
                               printConds conds ++ printStmntAttrSet ats ++ " .\n"

printRl :: Rule -> String
printRl (Rl t1 t2 conds ats) = "rl " ++ printTerm t1 ++ " => " ++ printTerm t2 ++
                               printConds conds ++ printStmntAttrSet ats ++ " .\n"

printSort :: Sort -> String
printSort (SortId q) = show q

printConds :: [Condition] -> String
printConds [] = ""
printConds cs = "if " ++ printCondsAux cs

printCondsAux :: [Condition] -> String
printCondsAux [] = ""
printCondsAux [c] = printCond c
printCondsAux (c : cs) = printCond c ++ " /\\ " ++ printCondsAux cs


printCond :: Condition -> String
printCond (EqCond t1 t2) = printTerm t1 ++ " = " ++ printTerm t2
printCond (MatchCond t1 t2) = printTerm t1 ++ " := " ++ printTerm t2
printCond (MbCond t s) = printTerm t ++ " : " ++ printSort s
printCond (RwCond t1 t2) = printTerm t1 ++ " => " ++ printTerm t2

printMorphism :: Map.Map Qid Qid -> Map.Map Qid (Map.Map ([Qid], Qid) (Qid, ([Qid], Qid))) -> Map.Map Qid Qid -> String 
printMorphism sorts ops labels = if str == ""
                            then ""
                            else "\n\nMorphism:\n\n" ++ str
    where str = (printQidMap "sort" sorts) ++ (printOpRenaming ops)
                ++ (printQidMap "label" labels)

printQidMap :: String -> Map.Map Qid Qid -> String
printQidMap str = Map.foldWithKey f ""
       where f = \ x y z -> str ++ " " ++ show x ++ " to " ++ show y ++ "\n" ++ z

printOpRenaming :: Map.Map Qid (Map.Map ([Qid], Qid) (Qid, ([Qid], Qid))) -> String
printOpRenaming = Map.foldWithKey f ""
       where f = \ x y z -> (Map.foldWithKey (g x) "" y) ++ z
                    where g = \ from (ar, co) (to, _) z' -> 
                                  "op " ++ show from ++ " : " ++ printArity ar ++ " -> "
                                  ++ show co ++ " to " ++ show to ++ z'
