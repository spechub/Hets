theory DataType
 
imports Main

begin

datatype 'a type1 =
       foo |
       bar "'a type2"
and 'a type2 = "a * nat * 'a type1"
and 'a type3 = "nat * 'a type2"

datatype ('a,'b) type6 = bar "'a * 'b"

consts
I :: "nat type1"

axioms
same_ax : "ALL (g1::'a=>'a) g2 a b. (a & ~b) --> g1 = g2"

lemma I: "A --> A"
proof
  assume A
  show A by fact
qed

end
