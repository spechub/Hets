theory Def
 imports Real
begin

type_synonym real_vector = "nat \<Rightarrow> real"

definition deviation ::
  "nat \<Rightarrow> real_vector \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real_vector" where
  "deviation n bid alternative_value index j \<equiv> if j = index then alternative_value else bid j"

end
