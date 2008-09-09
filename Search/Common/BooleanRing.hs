{- |
Module      :  $Header$
Description :  Boolean ring normalization. Intended to replace CNF in Common.Normalization
Copyright   :  (c) Immanuel Normann, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  inormann@jacobs-university.de
Stability   :  provisional
Portability :  portable
-}
module Search.Common.BooleanRing where

import Search.Common.Data
import qualified Data.List as L
import qualified Data.Set as S

{-
Functions
todo: Elimination von: imp, or , eqv, neg
      flatten, distr
-}


brForm :: (Show c, Show v, Ord v, Ord c) =>
          Formula (Constant c) v -> Formula (Constant c) v
brForm (Binder b vs body) = Binder b vs (brForm body)
brForm f = br -- reduce $ fromAlgebra f
    where (Const Xor ands) = reduce $ fromAlgebra f
          br = (Const Xor (map reduceAnd ands)) -- todo: this should be already performed in reduce
          reduceAnd (Const And xs) = (Const And (L.nub xs))
          reduceAnd f = f



fromAlgebra (Var v xs) = (Var v xs)
fromAlgebra (Const Not [x]) = Const Xor [Const TrueAtom [],fromAlgebra x]
fromAlgebra (Const Imp [x,y]) = fromAlgebra (Const Or [(Const Not [x]),y])
fromAlgebra (Const And xs) = Const And (map fromAlgebra xs)
fromAlgebra (Const Or [x]) = fromAlgebra x
fromAlgebra (Const Or (x:y:rest)) =
    fromAlgebra (Const Or ((Const Xor [x,y,(Const And [x,y])]):rest))
fromAlgebra (Const Eqv [x,y]) = fromAlgebra (Const Not [Const Xor [x,y]])
fromAlgebra (Const Xor xs) = Const Xor (map fromAlgebra xs)
fromAlgebra (Const TrueAtom []) = Const TrueAtom []
fromAlgebra (Const FalseAtom []) = Const FalseAtom []
fromAlgebra (Const Equal xs) =(Const Equal xs)
fromAlgebra (Binder _ _ _) = error "quantitfier free expression expected"
fromAlgebra f = error ("fromAlgebra: pattern not supported in " ++ show f)

reduce (Var x args) = (Var x args)
reduce (Const TrueAtom _) = (Const TrueAtom [])
reduce (Const FalseAtom _) = (Const FalseAtom [])
reduce (Const Xor [Const TrueAtom []]) = true -- stimmt das so?
reduce (Const Xor [x]) = reduce x -- stimmt das so?
reduce (Const Xor (Const FalseAtom []:rest)) = reduce (Const Xor rest)
reduce (Const Xor args) =
    let args1 = L.sort (map reduce args)
        reducePairs (x:y:rest) = 
            if x == y then (reducePairs rest)
               else x:(reducePairs (y:rest))
        reducePairs xs = xs
    in case pull Xor (filter (/=false) (reducePairs args1)) -- try to pull an Xor expression to front
       of ((Const Xor args2):rest) -> reduce (Const Xor (args2 ++ rest))
          [] -> Const FalseAtom [] -- stimmt das so?
          [Const FalseAtom []] -> Const FalseAtom [] -- stimmt das so?
          [Const TrueAtom []] -> Const TrueAtom [] -- stimmt das so?
          args3 -> Const Xor args3
reduce (Const And fs) =
    let fs' = L.nub $ L.sort $ map reduce fs
    in if elem false fs'
       then false
       else case pull And (filter (/=true) fs')  -- try to pull an And expression to front
            of [] -> true -- i.e. every component of fs was false so (Const And fs) is false
               [f] -> f  -- And with a single argument f is interpreted as f itself!!
               ((Const And ffs'):ffs) -> reduce (Const And (L.sort (ffs'++ffs)))
               ffs -> case pull Xor ffs
                      of ((Const Xor ffs'):ffs) -> reduce (Const Xor (distAnd ffs' ffs))
                         _ -> (Const And ffs)
reduce (Const Equal xs) =(Const Equal xs)
reduce x = error ("todo: " ++ show x)

distAnd l1 l2 = map (\x -> Const And (x:l2)) l1

pull op lst = pull' lst []
    where pull' [] acc = acc
          pull' ((Const op2 xs):ys) acc =
              if op == op2
              then ((Const op2 xs):ys)++acc
              else pull' ys ((Const op2 xs):acc)
          pull' (y:ys) acc = pull' ys (y:acc)

-- helpers

true :: Formula (Constant c) v
true = Const TrueAtom []
false :: Formula (Constant c) v
false = Const FalseAtom []


{-
Testing 

*Common.BooleanRing> t <- getTerm "implies(and(a,b),a)"
(imp (and "a" "b") "a")
*Common.BooleanRing> t
(imp (and "a" "b") "a")
*Common.BooleanRing> fromAlgebra t
(xor (xor true (and "a" "b")) "a" (and (xor true (and "a" "b")) "a"))
*Common.BooleanRing> reduce $ fromAlgebra t
true

t <- getTerm "xor(a,and(b,b),and(a,true))"

*Common.BooleanRing> t <- getTerm "xor(a,and(b,and(b,b)),and(a,true))"
(xor "a" (and "b" (and "b" "b")) (and "a" true))
*Common.BooleanRing> reduce t
"b"

*Common.BooleanRing> t <- getTerm "and(a,and(b,and(b,a)),and(a,true))"
(and "a" (and "b" (and "b" "a")) (and "a" true))
*Common.BooleanRing> reduce t
(and "a" "b")

*Common.BooleanRing> t <- getTerm "xor(a,b,c,b,c,c,a)"
(xor "a" "b" "c" "b" "c" "c" "a")
*Common.BooleanRing> reduce t
(xor "c")

*Common.BooleanRing> t <- getTerm "and(a,xor(b,c,d))"
(and "a" (xor "b" "c" "d"))
*Common.BooleanRing> reduce t
(xor (and "a" "b") (and "a" "c") (and "a" "d"))

*Common.BooleanRing> t <- getTerm "xor(a,a)"
(xor "a" "a")
*Common.BooleanRing> reduce t
false
*Common.BooleanRing> t <- getTerm "and(a,xor(b,and(a,c,a),xor(a,and(a,a))),and(a,b))"
(and "a" (xor "b" (and "a" "c" "a") (xor "a" (and "a" "a"))) (and "a" "b"))
*Common.BooleanRing> reduce t
(xor (and "a" "b") (and "a" "b" "c"))

*Common.BooleanRing> t <- reduceBTerm "implies(a,b)"
(xor "a" (and "b" "a") true)

*Common.BooleanRing> reduceBTerm "or(a,b,c)"
(xor "c" "b" "a" (and "c" "b" "a") (and "c" "b") (and "c" "a") (and "b" "a"))

*Common.BooleanRing> reduceBTerm "equiv(a,a)"
true

*Common.BooleanRing> getBTerm "equiv(implies(and(a,b),c),implies(a,implies(b,c)))"
(xor true (xor (xor (xor true (and "a" "b")) "c" (and (xor true (and "a" "b")) "c")) (xor (xor true "a") (xor (xor true "b") "c" (and (xor true "b") "c")) (and (xor true "a") (xor (xor true "b") "c" (and (xor true "b") "c"))))))

*Common.BooleanRing> reduceBTerm "equiv(implies(and(a,b),c),implies(a,implies(b,c)))"
true
-}

