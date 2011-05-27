theory MyList 
imports Main
begin

cd "/home/cxl/tex/grants/FormalSafe/isa2omdoc";
use "ROOT.ML";

section {* Types *}

text {* A type declaration: *}

typedecl mytype

text {* An algebraic datatype: *}

datatype 'a mylist = EmptyList                ("<>")
                   | ConsList 'a "'a mylist"  (infixr "##" 65) 

section {* Functions *}

consts 
  append :: "'a mylist => 'a mylist=> 'a mylist"   ("_ ++ _" [70, 70] 70)
primrec
 "<> ++ ys = ys"
 "(x##xs) ++ ys = (x ## (append xs ys))"

lemma app_nil_r: "xs ++ <> = xs"
 apply (induct_tac "xs")
 apply (simp+)
 done

ML_val {* ParseTerm.TermToOMOBJ (utility.getleaf(), [], "") (#prop (rep_thm (thm "app_nil_r"))) *}

ML_command {* val app_nil_r= thm "app_nil_r" *}

fun length :: "'a mylist => nat"  ("| _ |"  [70] 70)
where 
    "|<>| = 0"
  | "|(x ## xs)| = 1 + |xs|"

function merge :: "('a:: ord) mylist=> 'a mylist=> 'a mylist"
where
    "merge <> ys = ys"
  | "merge xs <> = xs" 
  | "merge (x##xs) (y##ys) = (if x < y then x ## merge xs (y## ys)
                                       else y ## merge (x##xs) ys)"
  by pat_completeness auto
  termination by (relation "measure (% (xs, ys). |xs| + |ys| )", auto)


function mergeBy :: "('a=> 'a=> bool)=> 'a mylist=> 'a mylist=> 'a mylist"
where
    "mergeBy ord <> ys = ys"
  | "mergeBy ord xs <> = xs" 
  | "mergeBy ord (x##xs) (y##ys) = (if ord x y then x ## mergeBy ord xs (y## ys)
                                              else y ## mergeBy ord (x##xs) ys)"
  by pat_completeness auto
  termination by (relation "measure (% (ord, xs, ys). |xs| + |ys| )", auto)

end


