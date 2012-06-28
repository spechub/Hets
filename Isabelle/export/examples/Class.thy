theory Class
 imports HOL Nat
begin

class parent =
 fixes p1 :: "'a => 'a => 'a"
 assumes a1: "p1 a b = p1 b a"

class parent2 =
 fixes p6 :: "'a"

class child1 = parent2

class empty

class child = parent + parent2 +
 fixes p2 :: "'a" and p3 :: "'a"
  and p4 p5 :: "'a"
 assumes a2: "p1 p2 x = x"
  and a3: "p1 x p2 = x"
  
end
