(* Taken from src/HOL/Enum.thy *)
theory Instantiation
imports Map
begin

class enum =
  fixes enum :: "'a list"
  fixes enum_all :: "('a \<Rightarrow> bool) \<Rightarrow> bool"
  fixes enum_ex :: "('a \<Rightarrow> bool) \<Rightarrow> bool"
  assumes UNIV_enum: "UNIV = set enum"
    and enum_distinct: "distinct enum"
  assumes enum_all_UNIV: "enum_all P \<longleftrightarrow> Ball UNIV P"
  assumes enum_ex_UNIV: "enum_ex P \<longleftrightarrow> Bex UNIV P"
   -- {* tailored towards simple instantiation *}
begin

subclass finite proof
qed (simp add: UNIV_enum)

lemma enum_UNIV:
  "set enum = UNIV"
  by (simp only: UNIV_enum)

end

instantiation "fun" :: (enum, equal) equal
begin

definition
  "HOL.equal f g \<longleftrightarrow> (\<forall>x \<in> set enum. f x = g x)"

instance proof
qed (simp_all add: equal_fun_def fun_eq_iff enum_UNIV)

end

end
