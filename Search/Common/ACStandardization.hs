{- |
Module      :  $Header$
Description :  Normalization w.r.t. associativity and commutativity
Copyright   :  (c) Immanuel Normann, Uni Bremen 2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  inormann@jacobs-university.de
Stability   :  provisional
Portability :  portable
-}
module Search.Common.ACStandardization where

import Search.Utils.List (updateListAndGetIndex)


type Arity = Int
type AC = Bool
data Symbol l v p = Logical l Arity AC
                  | Parameter p Arity AC
                  | Variable v Arity AC
                  | Lambda l Arity deriving (Show,Eq,Ord)

type State l v p = (([v], [p]), [Symbol l Int Int], [Symbol l v p])

acStandardize :: (Eq v, Ord l) =>
                 [Symbol l v p] -> ([Symbol l Int Int], [[Symbol l v p]])
acStandardize termStr = (acSkeleton,acParametrizations)
    where initMorph = ([],[])
          initPrefix = []
          initSuffix = termStr
          finalStates = pd [(initMorph,initPrefix,initSuffix)]
          ((_,acSkeleton,_):_) = finalStates
          third (_,_,p) = p
          acParametrizations = map third finalStates

pd states = case (head states)
            of (_,_,[]) -> states
               _ -> pd $ prun $ dist states

prun :: (Ord l) => [State l v p] -> [State l v p]
prun (s:states) = prun' [s] states
    where prun' minStates [] = minStates
          prun' (ms:minStates) (s:states) =
              let compStates (_,(p:_),_) (_,(q:_),_) = compare p q
              in case compStates ms s
                 of LT -> prun' (ms:minStates) states
                    EQ -> prun' (s:ms:minStates) states
                    GT -> prun' [s] states

dist :: (Eq v) => [State l v p] -> [State l v p]
dist states = concatMap dist1 states -- nub
    where dist1 (morph,prefix,suffix) =
              [succState (morph,prefix,suffix') | suffix' <- acPermuteSuffix suffix]

succState :: (Eq v) => State l v p -> State l v p
succState (morph,prefix,s:suffix) = (morph',(s':prefix),suffix)
    where (morph',s') = updateMorph morph s

updateMorph :: (Eq v) =>
               ([v], [p]) -> Symbol l v p -> (([v], [p]), Symbol l Int Int)
updateMorph (vlst,plst) s =
    case s
    of (Lambda l ar) -> ((vlst,plst),(Lambda l ar))
       (Logical l ar ac) -> ((vlst,plst),(Logical l ar ac))
       (Parameter p ar ac) -> ((vlst,p:plst),
                               (Parameter ((length plst) + 1) ar ac))
       (Variable v ar ac) -> ((vlst',plst),(Variable i ar ac))
           where (vlst',i) = updateListAndGetIndex v vlst
       

acPermuteSuffix :: [Symbol l v p] -> [[Symbol l v p]]
acPermuteSuffix [] = error "ac permutation requiers a non-empty list"
acPermuteSuffix suffix = if (isAC $ head suffix) then suffixes else [suffix]
    where (args,rest) = subterms suffix
          suffixes = map (((head suffix):) . (++rest)) (rotate args)

rotate :: [[a]] -> [[a]]
rotate lst = map concat $ map (per lst) [1..(length lst)]
    where per lst n = ys++xs where (xs,ys) = splitAt n lst

subterms :: [Symbol l v p] -> ([[Symbol l v p]], [Symbol l v p])
subterms lst = (reverse fss,bs)
    where (fss,bs) = sublists (arity $ head lst) ([],tail lst)
sublists n (fs,bs) = (fs',bs')
    where (fs',bs') = if n>=1 then sublists (n-1) (f:fs,bs'') else (fs,bs)
          (f,bs'') = subterm bs

subterm :: [Symbol l v p] -> ([Symbol l v p], [Symbol l v p])
subterm lst = ((reverse front),back)
    where (front,back) = sublist 0 ([],lst)
          sublist k (ms,n:ns) = 
              if k>=0
              then sublist ((arity n)+k-1) (n:ms,ns)
              else (ms,n:ns)


arity s = case s
          of (Lambda _ ar) -> ar
             (Logical _ ar _) -> ar
             (Parameter _ ar _) -> ar
             (Variable _ ar _) -> ar
             
isAC s = case s
         of (Lambda _ _) -> False
            (Logical _ _ ac) -> ac
            (Parameter _ _ ac) -> ac
            (Variable _ _ ac) -> ac

{- test
lst = [3,2,0,1,0,2,3,0,0,0,2,0,0,2,0,0,8,9,0]
-}


{- todo: 
   move this to Search.Common.Normalization.hs
   implement fromList
-}

data Formula c v = Const c [Formula c v] | Var v [Formula c v] 
                 | Binder c [v] (Formula c v) deriving (Eq,Ord)
data Constant c = TrueAtom | FalseAtom | Not | And | Or | Imp | Eqv | Xor | Equal
                | All | Some | LogicDependent c deriving (Eq,Ord)
data ScopeLabel a = Scope Int a deriving (Eq,Ord)

toList :: (Eq c) =>
          Formula (Constant c) (ScopeLabel p) -> [Symbol (Constant c) (ScopeLabel p) p]
toList (Binder c vs f) = ((Lambda c (length vs)):(map toList' vs))++(toList f)
    where toList' v = (Variable v 0 False)
    -- problem: arity of var in binding positioin unknown! Assume arity 0 i.e. FOL.
toList (Const c args) = (Logical c (length args) ac):(concatMap toList args)
    where ac = elem c [And,Or,Eqv,Xor,Equal]
toList (Var (Scope n v) args) = 
    case n of 0 -> (Parameter v (length args) False):(concatMap toList args)
              _ -> (Variable (Scope n v) (length args) False):(concatMap toList args)
