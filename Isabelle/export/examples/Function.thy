theory Function
 imports Definitions
begin

fun maximum ::
  "nat \<Rightarrow> real_vector \<Rightarrow> real" where
  "maximum 0 _ = 0" |
  "maximum (Suc n) y = max 0 (max (maximum n y) (y (Suc n)))"

fun testfun ::
  "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "testfun _ _ _ = 0"

fun testfun1 ::
 "nat \<Rightarrow> nat" where
 "testfun1 _ = 0"

end
