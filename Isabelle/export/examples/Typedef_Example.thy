theory Typedef_Example
imports Nat
begin

definition Pair_Rep :: "'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool" where
  "Pair_Rep a b = (\<lambda>x y. x = a \<and> y = b)"

definition "prod = {f. \<exists>a b. f = Pair_Rep (a\<Colon>'a) (b\<Colon>'b)}"

typedef ('a, 'b) prod (infixr "*" 20) = "prod :: ('a \<Rightarrow> 'b \<Rightarrow> bool) set"
  unfolding prod_def by auto

typedef nat = "{n. Nat n}"
  morphisms Rep_Nat Abs_Nat
  using Nat.Zero_RepI by auto

end
