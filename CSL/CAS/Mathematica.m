(* This library provides Mathematica functions needed for the
   Hets EnCL interface to Mathematica
 *)


(* binary minus *)
minus[x_, y_] := x - y;

(* unary minus *)
negate[x_] := -x;

(* fourth root *)
fthrt[x_] := Sqrt[Sqrt[x]];

(* this function is for representing floats as exact values *)
decodedFloat[x_, y_] := x*2^y;


(* maxloc/minloc:
   These procedures compute the location where the given function takes
   its maximum/minimum *)

maxloc[t_,x_,a_,b_] := ArgMax[{t, x >= a, x <= b}, x]

minloc[t_,x_,a_,b_] := ArgMin[{t, x >= a, x <= b}, x]


(* reldist:
   This procedure computes the relative distance of the arguments *)

reldist[t_, s_] := If [t==0 && s == 0, 0,  2*Abs[t-s]/(Abs[t] + Abs[s])]


(* reldistLe:
   This procedure computes if the relative distance of the first two argument
   is lower or equal to the third argument *)

reldistLe[t_, s_, e_] := If [t === undef, False, reldist[t,s] <= e]
