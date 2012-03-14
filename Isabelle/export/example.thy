theory example
 
imports Datatype 

begin

datatype (type4) type1 =
       foo |
       bar type2
and (type5) type2 = "nat * type1"
and type3 = "nat * type2"

datatype 'a type6 = bar 'a

consts
I :: type1

axioms
tt : "test --> test"

lemma I: "A --> A"
proof
  assume A
  show A by fact
qed

end
