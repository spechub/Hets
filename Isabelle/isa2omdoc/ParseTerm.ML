(* Signature *)
signature ParseTerm =
sig
    val TermToOMOBJ : CDLookup.environment -> term -> (string * CDLookup.environment)
end;

(* Datatype for the OMOBJ structure *)

structure ParseTerm : ParseTerm = 
struct
open utility
datatype attribute = name of string
		   | id of string
	           | cd of string
		   | cdbase of string
		   | class of string
	           | style of string

datatype omobj = OMS of attribute list
	       | OMV of attribute list
	       | OMA of attribute list * omobj list
	       | OMBIND of attribute list * omobj * omobj * omobj * typ
	       | OMBVAR of attribute list * omobj list

(* term -> omobj *)

exception index_overflow

fun get_attributes(OMBVAR(A, L)) = A


fun ith (0:int) (a::A) = a
|   ith n (a::A) = ith (n-1) A
|   ith _ nil  = raise index_overflow

val OMBase = CDLookup.isabelle_base();
val IsabelleCD = CDLookup.isabelle_cd();

(* V : List with Bound variables. TH : Theory of the term *)
(*#check theory to get cd right*)
fun termToomobj (Const(s,t)) V env = 
    let 
	val x = CDLookup.lookup (1, env) s
    in 
	(OMS([cdbase(OMBase),cd(#1 x),name(getName(s))]), #2 x)
    end
|   termToomobj (Free(s,t)) V  env = (if s = "" then say "fu0" else ();(OMV([name(s)]), env))
|   termToomobj (Var((s,0),t)) V env = (if s = "" then say "fu1" else (); (OMV([name(s)]), env))
|   termToomobj (Var((s,i),t)) V env = (if s = "" then say "fu2" else (); (OMV([name(s^Int.toString(i))]), env))
|   termToomobj (Bound(i)) V env = (OMV([name(ith i V)]), env)
|   termToomobj (Abs(s,t,scope)) V env = 
    let 
	val x = termToomobj scope (s::V) env
    in
	(OMBIND([], OMS([cdbase(OMBase),cd("Pure"),name("lambda")]), OMBVAR([],[OMV([name(s)])]), #1 x, t), #2 x)
    end
|   termToomobj (op$(Const(s1,t1),Abs(s2,t2,T))) V env = 
    let 
	val x = CDLookup.lookup (1, env) s1
	val y = termToomobj T (s2::V) (#2 x)
    in
	(OMBIND([], OMS([cdbase(OMBase),cd(#1 x),name(getName(s1))]), OMBVAR([],[OMV([name(s2)])]), #1 y, t2), #2 y)
    end
|   termToomobj (op$(T1,T2)) V env = 
    let 
	val x = termToomobj T1 V env
	val y = termToomobj T2 V (#2 x)
    in
	(OMA([],[#1 x, #1 y]), #2 y)
    end

(* Emitting the omobj type into a string *)
fun escape([])=[]| 
	    escape(namee)= if hd(namee)="&" then "&amp;"::escape(tl(namee)) else
			  if hd(namee)="<" then "&lt;"::escape(tl(namee)) else
			  if hd(namee)=">" then "&gt;"::escape(tl(namee)) else
			  if hd(namee)="\"" then "&quot;"::escape(tl(namee)) else
			  if hd(namee)="'" then "&apos;"::escape(tl(namee)) else hd(namee)::escape(tl(namee));
	fun escaped(namee)=implode(escape(explode(namee)));
fun ParseAtt(nil) = ""
|   ParseAtt(name(s)::A) = " name=\"" ^ escaped(s) ^ "\"" ^ ParseAtt(A)
|   ParseAtt(id(s)::A) = " id=\"" ^ escaped(s) ^ "\"" ^ ParseAtt(A)
|   ParseAtt(cd(s)::A) = " cd=\"" ^ escaped(s) ^ "\"" ^ ParseAtt(A)
|   ParseAtt(cdbase(s)::A) = " cdbase=\"" ^ escaped(s) ^ "\"" ^ ParseAtt(A)
|   ParseAtt(class(s)::A) = " class=\"" ^ escaped(s) ^ "\"" ^ ParseAtt(A)
|   ParseAtt(style(s)::A) = " style=\"" ^ escaped(s) ^ "\"" ^ ParseAtt(A)
fun addsecond(x::nil, y)=[(x,y)]|
    addsecond (x::xs, y) = (x,y)::addsecond(xs,y);
fun ParseObj (OMS(A), env) = ("<om:OMS" ^ ParseAtt(A) ^ "/>\n",[])
|   ParseObj (OMV(A), env) = ("<om:OMV" ^ ParseAtt(A) ^ "/>\n",[])
|   ParseObj (OMA(A,L), env) = 
	let
		fun unzip [] = ("",[])
		 |  unzip ((obj,var)::L) = 
		 	let 
		 		val (O,V) = unzip L
		 	in
		 		(obj^O,var@V)
		 	end
		val (objs, vars) = unzip (map ParseObj (addsecond(L,env)))
	in
		("<om:OMA" ^ ParseAtt(A) ^ ">\n" ^ objs  ^ "</om:OMA>\n", utility.uniquify (utility.mergesort op< vars))
	end

|ParseObj (OMBIND (A,quant,x,scope,T), env) =
	let
		val (typestring, tvars) = ParseTyp.TypToOMOBJ (T, env)
		val (obj1, vars1) = ParseObj (quant, env)
		val (obj2, vars2) = ParseObj (x, env)
		val (obj3, vars3) = ParseObj (scope, env)
	in
	(
		 "<om:OMBIND" ^ ParseAtt(A) ^ ">\n" ^
		 obj1 ^
		 "<om:OMBVAR" ^ ParseAtt(get_attributes(x)) ^ ">\n"^
		 	"<om:OMATTR>\n" ^ 
		 		"<om:OMATP>\n" ^ 
		 			"<om:OMS cdbase=\""^OMBase^"\" cd=\"Pure\" name=\"oftype\"/>\n" ^ 
					 typestring ^
		 		"</om:OMATP>\n" ^
		 		obj2 ^
			 "</om:OMATTR>\n" ^
		 "</om:OMBVAR>\n" ^
		 obj3 ^ 
		 "</om:OMBIND>\n"
	,utility.uniquify (utility.mergesort op< (tvars@vars1@vars2@vars3)))
	end

|ParseObj (OMBVAR (A,L),env) = 
	let
		fun unzip [] = ("",[])
		 |  unzip ((obj,var)::L) = 
		 	let 
		 		val (O,V) = unzip L
		 	in
		 		(obj^O,var@V)
		 	end
		val (objs, vars) = unzip (map ParseObj (addsecond(L,env)))
	in
		(objs, utility.uniquify (utility.mergesort op< vars))
	end
(* Emitting Terms into <OMOBJ> *)
fun TermToOMOBJ env T =
    let
	val x = termToomobj T [] env
	val (obj:string, tvars:string list) = ParseObj (#1 x, #2 x)
    in
	(
	if tvars = [] then obj else
	"<om:OMBIND>\n"
	^"<om:OMS cdbase=\""^OMBase^"\" cd=\"Pure\" name=\"alltype\"/>\n"
	^"<om:OMBVAR>\n"
	^(foldl op^ "" (map (fn x=>"<om:OMV name=\""^x^"\"/>\n") tvars))
	^"</om:OMBVAR>\n"
	^obj
	^"</om:OMBIND>\n"
	, #2 x)
    end
end;
