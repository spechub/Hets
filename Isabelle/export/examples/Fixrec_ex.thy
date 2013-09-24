(*  Title:      HOL/HOLCF/Tutorial/Fixrec_ex.thy
    Author:     Brian Huffman
*)

header {* Fixrec package examples *}

theory Fixrec_ex
imports HOLCF
begin

fixrec down :: "'a u \<rightarrow> 'a"
where "down\<cdot>(up\<cdot>x) = x"

fixrec from_sinl :: "'a \<oplus> 'b \<rightarrow> 'a"
where "x \<noteq> \<bottom> \<Longrightarrow> from_sinl\<cdot>(sinl\<cdot>x) = x"

fixrec from_sinl_up :: "'a u \<oplus> 'b \<rightarrow> 'a"
where "from_sinl_up\<cdot>(sinl\<cdot>(up\<cdot>x)) = x"

fixrec down2 :: "'a u \<times> 'b u \<rightarrow> 'a \<times> 'b"
where "down2\<cdot>(up\<cdot>x, up\<cdot>y) = (x, y)"

domain 'a llist = lNil | lCons (lazy 'a) (lazy "'a llist")

fixrec
  lzip :: "'a llist \<rightarrow> 'b llist \<rightarrow> ('a \<times> 'b) llist"
where
  "lzip\<cdot>(lCons\<cdot>x\<cdot>xs)\<cdot>(lCons\<cdot>y\<cdot>ys) = lCons\<cdot>(x, y)\<cdot>(lzip\<cdot>xs\<cdot>ys)"
| "lzip\<cdot>lNil\<cdot>lNil = lNil"

lemma lzip_stricts [simp]:
  "lzip\<cdot>\<bottom>\<cdot>ys = \<bottom>"
  "lzip\<cdot>lNil\<cdot>\<bottom> = \<bottom>"
  "lzip\<cdot>(lCons\<cdot>x\<cdot>xs)\<cdot>\<bottom> = \<bottom>"
by fixrec_simp+

lemma lzip_undefs [simp]:
  "lzip\<cdot>lNil\<cdot>(lCons\<cdot>y\<cdot>ys) = \<bottom>"
  "lzip\<cdot>(lCons\<cdot>x\<cdot>xs)\<cdot>lNil = \<bottom>"
by fixrec_simp+

fixrec
  from_sinr_up :: "'a \<oplus> 'b\<^sub>\<bottom> \<rightarrow> 'b"
where
  "from_sinr_up\<cdot>\<bottom> = \<bottom>"
| "from_sinr_up\<cdot>(sinr\<cdot>(up\<cdot>x)) = x"

fixrec
  seq :: "'a \<rightarrow> 'b \<rightarrow> 'b"
where
  "seq\<cdot>\<bottom>\<cdot>y = \<bottom>"
| "x \<noteq> \<bottom> \<Longrightarrow> seq\<cdot>x\<cdot>y = y"

fixrec
  lzip2 :: "'a llist \<rightarrow> 'b llist \<rightarrow> ('a \<times> 'b) llist"
where
  "lzip2\<cdot>(lCons\<cdot>x\<cdot>xs)\<cdot>(lCons\<cdot>y\<cdot>ys) = lCons\<cdot>(x, y)\<cdot>(lzip2\<cdot>xs\<cdot>ys)"
| (unchecked) "lzip2\<cdot>xs\<cdot>ys = lNil"

lemma lzip2_simps [simp]:
  "lzip2\<cdot>(lCons\<cdot>x\<cdot>xs)\<cdot>lNil = lNil"
  "lzip2\<cdot>lNil\<cdot>(lCons\<cdot>y\<cdot>ys) = lNil"
  "lzip2\<cdot>lNil\<cdot>lNil = lNil"
by fixrec_simp+

lemma lzip2_stricts [simp]:
  "lzip2\<cdot>\<bottom>\<cdot>ys = \<bottom>"
  "lzip2\<cdot>(lCons\<cdot>x\<cdot>xs)\<cdot>\<bottom> = \<bottom>"
by fixrec_simp+

domain 'a tree = Leaf (lazy 'a) | Branch (lazy "'a forest")
and    'a forest = Empty | Trees (lazy "'a tree") "'a forest"

fixrec
  map_tree :: "('a \<rightarrow> 'b) \<rightarrow> ('a tree \<rightarrow> 'b tree)"
and
  map_forest :: "('a \<rightarrow> 'b) \<rightarrow> ('a forest \<rightarrow> 'b forest)"
where
  "map_tree\<cdot>f\<cdot>(Leaf\<cdot>x) = Leaf\<cdot>(f\<cdot>x)"
| "map_tree\<cdot>f\<cdot>(Branch\<cdot>ts) = Branch\<cdot>(map_forest\<cdot>f\<cdot>ts)"
| "map_forest\<cdot>f\<cdot>Empty = Empty"
| "ts \<noteq> \<bottom> \<Longrightarrow>
    map_forest\<cdot>f\<cdot>(Trees\<cdot>t\<cdot>ts) = Trees\<cdot>(map_tree\<cdot>f\<cdot>t)\<cdot>(map_forest\<cdot>f\<cdot>ts)"

lemma map_tree_strict [simp]: "map_tree\<cdot>f\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

lemma map_forest_strict [simp]: "map_forest\<cdot>f\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

fixrec
  repeat :: "'a \<rightarrow> 'a llist"
where
  [simp del]: "repeat\<cdot>x = lCons\<cdot>x\<cdot>(repeat\<cdot>x)"

lemma repeat_simps [simp]:
  "repeat\<cdot>x \<noteq> \<bottom>"
  "repeat\<cdot>x \<noteq> lNil"
  "repeat\<cdot>x = lCons\<cdot>y\<cdot>ys \<longleftrightarrow> x = y \<and> repeat\<cdot>x = ys"
by (subst repeat.simps, simp)+

lemma llist_case_repeat [simp]:
  "llist_case\<cdot>z\<cdot>f\<cdot>(repeat\<cdot>x) = f\<cdot>x\<cdot>(repeat\<cdot>x)"
by (subst repeat.simps, simp)

fixrec
  inf_tree :: "'a tree" and inf_forest :: "'a forest"
where
  [simp del]: "inf_tree = Branch\<cdot>inf_forest"
| "inf_forest = Trees\<cdot>inf_tree\<cdot>(Trees\<cdot>inf_tree\<cdot>Empty)"

locale test =
  fixes foo :: "'a \<rightarrow> 'a"
  assumes foo_strict: "foo\<cdot>\<bottom> = \<bottom>"
begin

fixrec
  bar :: "'a u \<rightarrow> 'a"
where
  "bar\<cdot>(up\<cdot>x) = foo\<cdot>x"

lemma bar_strict: "bar\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

end

end
