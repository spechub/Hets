theory Consts 
imports Main
begin

consts f :: "nat => nat=> nat" 

defs f_meine_definition: "f x y == 2 *x+ y"

constdefs
   g :: "nat => nat"
   "g x == 4* x+ 1"

definition
  h :: "nat => nat"
where
 "h x = x+ x"

constdefs 
  k :: "nat=> nat=> (nat* nat) list"  ("<<_.._>>") 
 "<<a..b>> == [(a,b), (a, a), (b, a), (b, b)]"

syntax 
  xyz :: "nat=> nat"


lemma "length (<<x..y>>) == 4"
 apply (simp add: k_def, arith)
 done

end

