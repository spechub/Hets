theory MyListSimple
imports Main
begin

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

fun length :: "'a mylist => nat"  ("| _ |"  [70] 70)
where 
    "|<>| = 0"
  | "|(x ## xs)| = 1 + |xs|"
end


