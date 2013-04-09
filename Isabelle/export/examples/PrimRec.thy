theory PrimRec
imports Main
begin

datatype test = Test

primrec testFun :: "test => nat" where
"testFun Test = 0"

(* taken from HOL/Quickcheck_Examples/Hotel_Example.thy *)

datatype guest = Guest0 | Guest1
datatype key = Key0 | Key1 | Key2 | Key3
datatype room = Room0

type_synonym card = "key * key"

datatype event =
   Check_in guest room card | Enter guest room card | Exit guest room

primrec owns :: "event list \<Rightarrow> room \<Rightarrow> guest option"
where
  "owns [] r = None"
| "owns (e#s) r = (case e of
    Check_in g r' c \<Rightarrow> if r' = r then Some g else owns s r |
    Enter g r' c \<Rightarrow> owns s r |
    Exit g r' \<Rightarrow> owns s r)"

(* taken from https://lists.cam.ac.uk/pipermail/cl-isabelle-users/2009-February/msg00019.html *)

datatype 'a form = ff | Cpd "'a" "'a form list"

primrec max_list :: "nat list => nat" where
  "max_list []       = 0"
| "max_list (i # is) = max i (max_list is)"

primrec depth :: "'a form => nat" and depth_list :: "'a form list => nat list" where
  "depth ff = 0"
| "depth (Cpd f fs) = max_list (depth_list fs) + 1"
| "depth_list [] = []"
| "depth_list (f # fs) = depth f # depth_list fs"

end
