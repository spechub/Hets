(* Taken from http://cl-informatik.uibk.ac.at/users/clemens/publications/types2003.pdf *)
theory Locale
 imports HOL
begin

locale semi =
 fixes prod :: "['a, 'a] => 'a" (infixl "*" 70)
 and test
 assumes assoc: "(x * y) * z = x * (y * z)"

locale comm_semi = semi +
 assumes comm: "x * y = y * x"
 and test: "False=x & ~x"
 and test1: "y=y"
 and test2: "x=x"

locale parent
locale parent1

locale child = parent + parent1

end
