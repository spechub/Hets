signature CDLookup =
sig
    type environment
    val lookup : (int * environment) -> string -> (string * environment)
    val isabelle_cd : unit -> string
    val isabelle_base : unit -> string
end;

structure CDLookup : CDLookup = 
struct
exception UNDECLARED_CONST
exception UNDECLARED_CLASS

type environment = (utility.bstree * theory list *string)

fun isabelle_cd () = "http://cds.omdoc.org/logics/isabelle.omdoc?Pure"
fun isabelle_base () = "http://cds.omdoc.org/logics/isabelle.omdoc"


fun find_first [] const = raise UNDECLARED_CONST
  | find_first (thy::thyList) const = 
    if Sign.declared_const thy const orelse Sign.declared_tyname thy const
       then Context.theory_name thy
    else 
	find_first thyList const


fun find_first_class [] class_name = raise UNDECLARED_CLASS|
    find_first_class (thy::thyList) class_name =
	if utility.member (Sign.all_classes thy) class_name then Context.theory_name thy 
	else find_first_class (thyList) class_name;

fun lookup (opt, env) const = 
    let 
	val cd1 = utility.search (#1 env)  const
    in
	if cd1 <> "FAIL"
	   then (cd1, env)
	else
	if opt=1 then
	    let
		val cd2 = find_first (#2 env) const
	    in
		(cd2, ((utility.insert (#1 env) (const,cd2)), #2 env, #3 env))
	    end
	 else 
	     let
		val cd2 = find_first_class (#2 env) const
	    in
		(cd2, ((utility.insert (#1 env) (const,cd2)), #2 env, #3 env))
	    end
    end

	
   
end;
