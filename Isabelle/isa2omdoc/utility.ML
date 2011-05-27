signature utility =
sig
    type bstree
    val getleaf : unit -> bstree
    val mergesort : ('a * 'a -> bool) -> 'a list -> 'a list
    val uniquify : ''a list -> ''a list
    val rem : ''a list * ''a list -> ''a list 
    val insert : bstree -> string * string -> bstree
    val search : bstree -> string -> string
    val getName : string -> string
    val say : string -> unit
    val member : ''a list -> ''a -> bool
	     
end;

structure utility : utility = 
struct

fun member nil _ = false | 
    member (x::xs) y = if x = y then true else (member xs y)
fun say s = TextIO.output(TextIO.stdOut, s^"\n")

(*mergesort*)
	fun getDot (nil) = nil|
	    getDot ("."::x) = nil|
	    getDot (a::x) = a::(getDot(x))
	val getName = implode o rev o getDot o rev o explode
fun mergesort comp [] = []
  | mergesort comp (m::[]) = [m]
  | mergesort comp (m::M) = 
    let
	fun partition (A, B, []) = (A,B)
	  | partition (A, B, a :: []) = (a::A, B)
	  | partition (A, B, a :: b :: C) = partition (a::A, b::B, C);
	val (A,B) = partition([], [], m::M)
	val C = mergesort comp A
	val D = mergesort comp B
	fun merge([], B, M) = M @ B
	  | merge(A, [], M) = M @ A
	  | merge(a::A, b::B, M) = if comp (a, b)
				   then merge(A, b::B, M@[a])
				   else
				       merge(a::A, B, M@[b]);
    in
	merge(C,D,[])
    end
(* make elements in an ordered list unique *)
fun uniquify [] = []
  | uniquify (a::[]) = [a]
  | uniquify (a::b::A) = if a = b 
		           then uniquify (b::A)
		       else
			   a :: uniquify (b::A)

(* remove all elements in A from B. A must be a subset of B and the lists have to be ordered with each element being unique *)
fun rem ([], B) = B
  | rem (A, []) = []
  | rem (a::A, b::B) = if op=(a,b)
			  then rem(A, B)
		       else
			   b :: rem(a::A, B)

(* Binary search tree for storing (constant, CD) pairs*)
datatype bstree = leaf | node of string * string * bstree * bstree

fun insert leaf (const,CD) = node(const,CD,leaf,leaf)
  | insert (node(const1, CD1, L, R)) (const2, CD2) = 
    if const1 < const2
       then node(const1, CD1, L, (insert R (const2, CD2)))
    else
	node(const1, CD1, (insert L (const2, CD2)), R)

fun search leaf query = "FAIL"
  | search (node(const, CD, L, R)) query = 
    if const = query 
        then CD
    else 
	if const < query
	    then search R query
	else
	    search L query
fun getleaf () = leaf

end;
(*
Control.Print.printDepth := 100; 
*)
