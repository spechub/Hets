

signature ThyToOMDoc = 
sig
    val ParseTheory : string -> unit*unit
end;

structure ThyToOMDoc : ThyToOMDoc = 
struct
open utility
fun escape([])=[]| 
	    escape(name)= if hd(name)="&" then "&amp;"::escape(tl(name)) else
			  if hd(name)="<" then "&lt;"::escape(tl(name)) else
			  if hd(name)=">" then "&gt;"::escape(tl(name)) else
			  if hd(name)="\"" then "&quot;"::escape(tl(name)) else
			  if hd(name)="'" then "&apos;"::escape(tl(name)) else hd(name)::escape(tl(name));
	fun escaped(name)=implode(escape(explode(name)));
(* Parsing Definitions *)
fun own_defs_of T = 
    let
	val get_defs = Defs.all_specifications_of o Theory.defs_of
	fun comp ((a,b), (x,y)) = a < x
	val defs = utility.mergesort comp (get_defs T)
	val ancestor_defs = utility.uniquify (utility.mergesort comp (foldl op@ [] (map get_defs (Context.ancestors_of T))))
    in
	utility.rem(ancestor_defs, defs)
    end

(* Parsing Constants *)
fun own_consts_of T = 		  
    let 
	val get_consts = NameSpace.dest_table o #constants o Consts.dest o Sign.consts_of
	fun comp ((a,b), (x,y)) = a < x
	val consts = utility.mergesort comp (get_consts T)
	val ancestor_consts = utility.uniquify (utility.mergesort comp (foldl op@ [] (map get_consts (Context.ancestors_of T))))
    in
	utility.rem(ancestor_consts, consts)
    end

fun get_term env Name (nil:(string * term) list) = ("",env)
  | get_term env Name (a::Axioms) = 
    if Name = (#1 a) orelse implode ((explode (#3 env) @ ["."] @ (explode Name))) = (#1 a)
        then let 
	    val x = ParseTerm.TermToOMOBJ env (#2 a)
	in
	    ("<definition name=\""^ escaped(getName(#1 a)) ^"\">\n" ^ (#1 x) ^ "</definition>\n", #2 x)
	end
    else get_term env Name Axioms

fun ParseConst env Axioms (Name, (Typ, Definition)) = 
    let 
	val def = fn NONE => get_term env (implode ((explode Name) @ (explode "_def"))) Axioms
		   | SOME(T) => 
		     let 
			 val x = ParseTerm.TermToOMOBJ env T
		     in
			 ("<definition>\n" ^ (#1 x) ^ "</definition>\n", #2 x)
		     end
	val y = def(Definition)
	val (obj, tvars) = ParseTyp.TypToOMOBJ (Typ, env)
    in
	("<constant name=\"" ^ escaped(getName(Name)) ^ "\">\n"
	^ "<type>\n"
	
	^ (if tvars = [] then obj else
	"<om:OMBIND>\n"
	^"<om:OMS cd=\"Pure\" name=\"alltype\"/>\n"
	^"<om:OMBVAR>\n"
	^(foldl op^ "" (map (fn x=>"<om:OMV name=\""^x^"\"/>\n") tvars))
	^"</om:OMBVAR>\n"
	^obj
	^"</om:OMBIND>\n")
	^ "</type>\n"
	^ (#1 y)			      
	^ "</constant>\n",
	 #2 y)
    end

fun ParseConsts env Axioms = 
    let 
	fun myfold env [] = ("", env)
	  | myfold env (c::constList) = 
	    let 
		val x= myfold env constList
		val y = ParseConst (#2 x) Axioms c
	    in
		((#1 y) ^ (#1 x), #2 y)
	    end
    in
	myfold env (own_consts_of (ThyInfo.get_theory (#3 env)))
    end
(* Parsing Axioms *)
fun own_axioms_of T = 
    let
	val get_axioms = Theory.axioms_of
	fun comp ((a,b), (x,y)) = a < x
	val axioms = utility.mergesort comp (get_axioms T)
	val ancestor_axioms = utility.uniquify (utility.mergesort comp (foldl op@ [] (map get_axioms (Context.ancestors_of T))))
	fun is_def ("f"::"e"::"d"::"_"::s) = true
	  | is_def _ = false
	fun divide (ax,def) (nil:(string * term) list) = (ax,def)
	  | divide (ax,def) (l::list) = if is_def (rev (explode (#1 l))) 
				      then divide (ax, l::def) list
				      else divide (l::ax, def) list
    in
	divide ([],[]) (utility.rem(ancestor_axioms, axioms))
    end

fun ParseAxiom env (s,t) = 
    let
	val x = ParseTerm.TermToOMOBJ env t
    in
	("<assertion name=\""^escaped(utility.getName s)^"\" role=\"axiom\">\n"^
	"<FMP>\n"^
	(#1 x)^
	"</FMP>\n"^
	"</assertion>\n",
	 (#2 x))
    end

fun ParseAxioms env = 
    let 
	fun myfold env [] = ("", env)
	  | myfold env (a::axiomList) = 
	    let 
		val x= myfold env axiomList
		val y = ParseAxiom (#2 x) a
	    in
		((#1 y) ^ (#1 x), #2 y)
	    end
    in
	myfold env (#1 (own_axioms_of (ThyInfo.get_theory (#3 env))))
    end

(* Parsing Theorems *)
fun own_theorems_of T =
    let 
	 fun get_theorems T = 
	
	
   		map (fn (a,b) => (a, prop_of b)) (PureThy.all_thms_of T)
	
	fun comp ((a,b), (x,y)) = a < x
	val theorems = utility.mergesort comp (get_theorems T)
	

	val debug=map get_theorems (Context.ancestors_of T)
	fun member(x,[])=false|
	    member(x,y::ys)=if x=y then true else member(x,ys);
	fun combine2(x::xs, [])=x::xs|
	    combine2(x::xs, y::ys)=if member(x,y::ys) then combine2(x::xs,ys) else combine2(y::x::xs,ys);
	fun combine((x::xs)::nil)=x::xs|
	    combine((x::xs)::ys)= combine(combine2(x::xs,hd(ys))::tl(ys));
	
	
	val debug2=combine(debug);
	val debug3 = utility.mergesort comp (debug2)
	val ancestor_theorems = utility.uniquify (debug3) 
    in
	utility.rem(ancestor_theorems, theorems)
    end

fun ParseTheorem env k t  = 
    let
	val x = ParseTerm.TermToOMOBJ env t
	fun def ("f"::"e"::"d"::"_"::_) = true
	  | def _ = false
	fun is_def s = def (rev (explode s))
    in
	if is_def k 
	then ("", env)
	else 
	("<assertion name=\""^escaped(getName(k))^"\" role=\"lemma\">\n"^
	"<FMP>\n"^
	(#1 x)^
	"</FMP>\n"^
	"</assertion>\n",
	(#2 x))
    end

fun ParseTheorems env =
    let
	
fun myfold env [] = ("", env)
          | myfold env ((k, t)::thmsList) = 
            let 
		
                val x = myfold env thmsList
                val y = ParseTheorem (#2 x) k t
            in
                ((#1 y) ^ (#1 x), #2 y)
            end
    in
	myfold env (own_theorems_of (ThyInfo.get_theory (#3 env)))
    end

(* Parsing Theories *)

fun ParseTheory S = 
    let
	val inputfile= TextIO.openIn(S ^ ".thy");
	fun getToImportLine(inputfile) = let
		val firstword = TextIO.inputN(inputfile,8);
		in if firstword="imports " then TextIO.inputLine(inputfile) 
			else let
				val inpufile2=TextIO.inputLine(inputfile)  (* check what happens if no import line*)
				in getToImportLine(inputfile)
			end
		end
	fun getImportNames(line: string option)=
		case line of
			NONE => ""|
			SOME(str) => str;
	fun tmp (x::xs:string list,y:string list) = if x<> " " andalso x<> "\n" then tmp(xs,x::y) else (xs,implode(rev(y))); 
	fun parseImportNames([],x)=x|
	    parseImportNames(str,x)= let
			val word= #2(tmp(str,[]))
			val remaining = #1 (tmp(str,[]))			
				in parseImportNames(remaining, word::x)
			end
	val importNames = (parseImportNames(explode(getImportNames(getToImportLine(inputfile))),[]));	
	
	fun printimports ([]) ="" |
	    printimports(x::xs) = "<imports from=\""^escaped(x)^"\"/>\n"^printimports(xs);
	
	fun get_name [] = ""
	  | get_name ("/" :: L) = ""
	  | get_name (a :: L) = (get_name L) ^ a
	val name = get_name(rev(explode(S)))

	val allimports = printimports(importNames);
	val tmp = TextIO.output(TextIO.stdOut, name);
	val xyz = if (ThyInfo.known_thy name) then () else use_thy S
        val T = ThyInfo.get_theory name
	val env = (utility.getleaf (), (rev (Context.ancestors_of T)) @ [T], name)
	val CONSTS = ParseConsts env (#2 (own_axioms_of T)) (* Why #2 and not #1 ?! #2 - definitions, #1 - axioms*)
	val AXIOMS = ParseAxioms (#2 CONSTS)
	val THEOREMS = ParseTheorems (#2 AXIOMS)
	val omdoc = "<omdoc xmlns=\"http://omdoc.org/ns\" xmlns:om=\"http://www.openmath.org/OpenMath\">\n" ^
		    "<theory name=\"" ^ escaped(S) ^ "\" meta=\"" ^ escaped(CDLookup.isabelle_cd()) ^ "\">\n" ^
		    allimports^
		    (#1 CONSTS) ^ (#1 AXIOMS) ^ (#1 THEOREMS) ^
		    "</theory>\n" ^
		    "</omdoc>\n"
	    handle index_overflow => "Index overflow"
	    handle UNDECLARED_CONST => "Found undeclared constant"
	val outs = TextIO.openOut (S^".omdoc")
    in
	(TextIO.output(outs, omdoc), TextIO.closeOut(outs))
    end
end;


(*
 src/HOL/Tools/datatype...

 add_datatype
*)
