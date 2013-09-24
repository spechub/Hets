theory Lemma
 
imports Main

begin

lemma I: "A --> A"
proof
  assume A
  show A by fact
qed

lemma shows      I1: "A --> A" (is "?B --> ?C" is "?D --> ?F")
                     "A --> A"
             and     "A --> A" by auto

end
