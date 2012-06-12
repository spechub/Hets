theory example
 
imports Datatype 

begin

datatype (type4) 'a type1 =
       foo |
       bar "'a type2"
and (type5) 'a type2 = "a * nat * 'a type1"
and 'a type3 = "nat * 'a type2"

datatype 'a type6 = bar 'a

consts
I :: "nat type1"

axioms
tt : "test --> test"
same_ax : "ALL (g1::'a=>'a) g2 a b. (a & ~b) --> g1 = g2"

lemma I: "A --> A"
proof
  assume A
  show A by fact
qed

end
