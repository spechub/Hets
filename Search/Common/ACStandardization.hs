{- |
Module      :  $Header$
Description :  Normalization w.r.t. associativity and commutativity
Copyright   :  (c) Immanuel Normann, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  inormann@jacobs-university.de
Stability   :  provisional
Portability :  portable
-}
module Search.Common.ACStandardization where

import Search.Utils.List (updateListAndGetIndex)

data Symbol = S Integer deriving (Show,Ord,Eq)

arity (S n) = n

subterm lst = ((reverse front),back)
    where (front,back) = sublist 0 ([],lst)
sublist k (ms,n:ns) = (ms',ns')
    where (ms',ns') = if k>=0 then sublist ((arity n)+k-1) (n:ms,ns) else (ms,n:ns)


nsubterms (n:lst) = (n,reverse fss,bs)
    where (fss,bs) = nsublists (arity n) ([],lst)
nsublists n (fs,bs) = (fs',bs')
    where (fs',bs') = if n>=1 then nsublists (n-1) (f:fs,bs'') else (fs,bs)
          (f,bs'') = subterm bs

rotate lst = map concat $ map (per lst) [1..(length lst)]
    where per lst n = ys++xs where (xs,ys) = splitAt n lst

rotateArgs lst = (n, map (prepend rest) (rotate args))
    where (n, args, rest) = nsubterms lst
          prepend ys xs = xs++ys

dist (morph,prefix,(s:suffix)) = 
    if isAC s then map (prepend rest) (rotate args) else [(morph,prefix,(s:suffix))]
        where (p, args, rest) = nsubterms suffix
              prepend ys xs = (morph,p:prefix,xs++ys)


isAC _ = True -- temp

data Symb c p = V c | P p | B p

succ (vlst,plst) (V s) = (i,vlst',plst)
    where (vlst',i) = updateListAndGetIndex s vlst
succ (vlst,plst) (P p) = (((length plst)+1),vlst,(plst++[p]))
succ (vlst,plst) (B _) = (0,vlst,plst)

{- test

-}
lst = [3,2,0,1,0,2,3,0,0,0,2,0,0,2,0,0,8,9,0]