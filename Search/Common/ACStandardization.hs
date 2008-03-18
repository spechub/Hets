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

arity = id
isAC _ = True

type Arity = Int
type AC = Bool
data Symbol l v p = Logical l Arity AC
                | Parameter p Arity AC
                | Variable v Arity AC
                | Lambda l

{-
acStandardize termStr = (acSkeleton,acParametrizations)
    where initMorph = ([],[])
          initPrefix = []
          initSuffix = termStr
          finalStates = (initMorph,initPrefix,initSuffix)
          ((_,acSkeleton,_):_) = finalStates
          thrd (_,_,p) = p
          acParametrizations = map thrd finalStates
-}

pd states = case (head states)
            of (_,_,[]) -> states
               _ -> pd $ prun $ dist states

prun (s:states) = prunAcc [s] states

prunAcc minStates [] = minStates
prunAcc (ms:minStates) (s:states) =
    let compStates (_,(p:_),_) (_,(q:_),_) = compare p q
    in case compStates ms s
       of LT -> prun (ms:minStates) states
          EQ -> prun (s:ms:minStates) states
          GT -> prun [s] states

dist states = concatMap dist1 states -- nub

dist1 (morph,prefix,suffix) =
    [succState (morph,prefix,suffix') | suffix' <- acPermuteSuffix suffix]

succState (morph,prefix,s:suffix) = (morph',(s':prefix),suffix)
    where (morph',s') = updateMorph morph s

updateMorph (vlst,plst) (Parameter p ar ac) = ((vlst,p:plst),s) -- ((vlst,plst++[p]),s)
    where s = (Parameter ((length plst) + 1) ar ac)
updateMorph (vlst,plst) (Variable v ar ac) = ((vlst',plst),s)
    where (vlst',i) = updateListAndGetIndex v vlst
          s = (Variable i ar ac)
updateMorph morph s = (morph,s)

acPermuteSuffix [] = error "ac permutation requiers a non-empty list"
acPermuteSuffix suffix = if (isAC $ head suffix) then suffixes else [suffix]
    where (args,rest) = subterms suffix
          suffixes = map (((head suffix):) . (++rest)) (rotate args)

rotate lst = map concat $ map (per lst) [1..(length lst)]
    where per lst n = ys++xs where (xs,ys) = splitAt n lst

subterms lst = (reverse fss,bs)
    where (fss,bs) = sublists (arity $ head lst) ([],tail lst)
sublists n (fs,bs) = (fs',bs')
    where (fs',bs') = if n>=1 then sublists (n-1) (f:fs,bs'') else (fs,bs)
          (f,bs'') = subterm bs

subterm lst = ((reverse front),back)
    where (front,back) = sublist 0 ([],lst)
sublist k (ms,n:ns) = (ms',ns')
    where (ms',ns') = if k>=0 then sublist ((arity n)+k-1) (n:ms,ns) else (ms,n:ns)


{-
dist = concatMap dist1
dist1 (morph,prefix,[]) = [(morph,prefix,[])]
dist1 (morph,prefix,(s:suffix)) =
    if isAC s
    then let (args, rest) = subterms (s:suffix)
             prepend ys xs = (morph,s:prefix,xs++ys)
         in map (prepend rest) (rotate args)
    else [(morph,s:prefix,suffix)]

-}


{-
 test

-}
lst = [3,2,0,1,0,2,3,0,0,0,2,0,0,2,0,0,8,9,0]
--slst = map f lst where f n = (C 'c' n True)