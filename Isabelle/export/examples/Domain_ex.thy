(*  Title:      HOL/HOLCF/Tutorial/Domain_ex.thy
    Author:     Brian Huffman
*)

header {* Domain package examples *}

theory Domain_ex
imports HOLCF
begin

domain d1 = d1a | d1b "d1" "d1"

lemma "d1b\<cdot>\<bottom>\<cdot>y = \<bottom>" by simp

domain d2 = d2a | d2b (lazy "d2")

lemma "d2b\<cdot>x \<noteq> \<bottom>" by simp

domain d3 = d3a | d3b (lazy "d2") "d2"

lemma "P (d3b\<cdot>x\<cdot>y = \<bottom>) \<longleftrightarrow> P (y = \<bottom>)" by simp

domain d4 = d4a | d4b (lazy d4b_left :: "d2") (d4b_right :: "d2")

lemma "y \<noteq> \<bottom> \<Longrightarrow> d4b_left\<cdot>(d4b\<cdot>x\<cdot>y) = x" by simp

domain d5 = d5a | d5b (lazy "d5") "d5" (infixl ":#:" 70)

lemma "d5a \<noteq> x :#: y :#: z" by simp

domain ('a, 'b) lazypair (infixl ":*:" 25) =
  lpair (lazy lfst :: 'a) (lazy lsnd :: 'b) (infixl ":*:" 75)

lemma "\<forall>p::('a :*: 'b). p \<sqsubseteq> lfst\<cdot>p :*: lsnd\<cdot>p"
by (rule allI, case_tac p, simp_all)

domain ('a, 'b) d6 = d6 "int lift" "'a \<oplus> 'b u" (lazy "('a :*: 'b) \<times> ('b \<rightarrow> 'a)")

domain 'a d7 = d7a "'a d7 \<oplus> int lift" | d7b "'a \<otimes> 'a d7" | d7c (lazy "'a d7 \<rightarrow> 'a")
  -- "Indirect recursion detected, skipping proofs of (co)induction rules"

domain 'a slist = SNil | SCons 'a "'a slist"

domain 'a stree = STip | SBranch "'a stree slist"

domain d8 = d8a | d8b "d9" and d9 = d9a | d9b (lazy "d8")

domain ('a, 'b) list1 = Nil1 | Cons1 'a "('b, 'a) list2"
   and ('b, 'a) list2 = Nil2 | Cons2 'b "('a, 'b) list1"

domain 'a flattree = Tip | Branch "'a flattree" "'a flattree"

lemma "\<lbrakk>P \<bottom>; P Tip; \<And>x y. \<lbrakk>x \<noteq> \<bottom>; y \<noteq> \<bottom>; P x; P y\<rbrakk> \<Longrightarrow> P (Branch\<cdot>x\<cdot>y)\<rbrakk> \<Longrightarrow> P x"
by (rule flattree.induct) -- "no admissibility requirement"

domain triv = Triv triv triv

lemma "(x::triv) = \<bottom>" by (induct x, simp_all)

domain natlist = nnil | ncons (lazy "nat discr") natlist

domain ('a::predomain) box = Box (lazy 'a)

domain ('a::countable) stream = snil | scons (lazy "'a discr") "'a stream"

domain 'a tree = Leaf (lazy 'a) | Node (left :: "'a tree") (right :: "'a tree")

end
