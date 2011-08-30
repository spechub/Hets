signature ExportHelper =
sig
	val get_consts : theory -> (string * (typ * term option)) list
	val get_axioms : theory -> (string * term) list
	val get_theorems : theory -> (string * term) list
	val get_datatypes : theory -> (string * (Datatype.info option)) list
	val get_generated_theorems : theory -> (string * (Datatype.info option)) list -> string list
	val filter : string list -> (string * 'a) list -> (string * 'a) list
end;

structure ExportHelper : ExportHelper =
struct
	fun id x = x
	fun mergesort _ []  	   = []
	  | mergesort _ [x] 	   = [x]
	  | mergesort cmp_data xs  = let val (ys,zs) = List.foldl (fn(i, (ys,zs)) => (zs, i::ys)) ([],[]) xs
			          	 fun merge (xs,[]) = xs
				    	   | merge ([],xs) = xs
				    	   | merge (x::xr,y::yr) = if (cmp_data x) <= (cmp_data y)
									then x::merge(xr,y::yr)
								   else y::merge(x::xr,yr)
			      	     in merge(mergesort cmp_data ys, mergesort cmp_data zs) end
	(* make a sorted list unique*)
	fun unique [] 		= []
          | unique [x]		= [x]
          | unique (x1::x2::xr) = if x1 = x2
                                   then unique (x2::xr)
                                  else x1::(unique (x2::xr))
	(* remove xs from ys - both lists need to be sorted asc *)
	fun remove' _ _ ([],ys)           = ys
	  | remove' _ _ (_,[])		  = []
	  | remove' cd1 cd2 (x::xr,y::yr) = if (cd1 x) < (cd2 y)
		 				then remove' cd1 cd2 (xr,y::yr)
		  		     	    else if (cd2 y) < (cd1 x)
						then y::(remove' cd1 cd2 (x::xr,yr))
				     	    else remove' cd1 cd2 (xr,yr)
	fun remove cmp_data = remove' cmp_data cmp_data
	fun remove_parent_data df cmp_data T = let val d  = df T
					           val pd = (List.foldl op@ [] (map df (Context.parents_of T)))
                                      	       in remove cmp_data (mergesort cmp_data pd,mergesort cmp_data d) end
	val get_consts = let val consts_of = Name_Space.dest_table o #constants o Consts.dest o Sign.consts_of
			 in remove_parent_data consts_of #1 end
	val get_axioms = remove_parent_data Theory.axioms_of #1
	val get_theorems = let fun theorems_of T =  map (fn (a,b) => (a, prop_of b)) (Global_Theory.all_thms_of T)
			   in remove_parent_data theorems_of #1 end
	fun get_datatypes T = let val tname = Context.theory_name T
			          val tl = String.size tname
                                  val ts = (#log_types o Type.rep_tsig o Sign.tsig_of) T
                               in map (fn s => (String.extract (s,tl+1,NONE),Datatype.get_info T s)) (List.filter (String.isPrefix tname) ts) end
	fun full_name T name = Name_Space.full_name (Sign.naming_of T) (Binding.name name)
        fun is_mutually_rec_type T (n,SOME(i)) = (case (#alt_names i) of SOME(names) => List.exists
                                                                                        (Option.isSome o (Datatype.get_info T) o (full_name T))
                                                                                        names
                                                                      | NONE => false)
          | is_mutually_rec_type _ (_,NONE) = false
	fun get_generated_theorems T ts =
         let fun get_ths (n,info) =
          let val alt_names = case (#alt_names info) of
                               SOME(names) => n::(List.filter (Option.isSome o (Datatype.get_info T) o (full_name T)) names)
                              | NONE => [n]
              val is' = List.map ((Datatype.get_info T) o (full_name T)) alt_names
              val is = List.map Option.valOf is'
              fun thms  i g = List.foldl (fn (get_thm, l1) => (Thm.derivation_name (get_thm i))::l1) [] g
              fun thmss i g = List.foldl (fn (get_thms,l1) => (List.map Thm.derivation_name (get_thms i)@l1)) [] g
	      val thms1 = List.foldl
                                  (fn (i,l) => (thms  i [#induct,#exhaust,#nchotomy,#case_cong,#weak_case_cong,#split,#split_asm])
                                              @(thmss i [#inject,#distinct,#inducts,#rec_rewrites,#case_rewrites])@l)
                           [] is
	      val new_type_names = the_default [n] (#alt_names info)
	      (*
 cf. http://isabelle.in.tum.de/repos/isabelle/file/6d736d983d5c/src/HOL/Tools/Datatype/datatype_data.ML#l329
     http://isabelle.in.tum.de/repos/isabelle/file/6d736d983d5c/src/HOL/Tools/Datatype/datatype_data.ML#l338 
     http://isabelle.in.tum.de/repos/isabelle/file/6d736d983d5c/src/Pure/global_theory.ML#l168
      http://isabelle.in.tum.de/repos/isabelle/file/6d736d983d5c/src/Pure/global_theory.ML#l162
       http://isabelle.in.tum.de/repos/isabelle/file/6d736d983d5c/src/Pure/global_theory.ML#l158
	http://isabelle.in.tum.de/repos/isabelle/file/6d736d983d5c/src/Pure/global_theory.ML#l139 *)
	      val prfx = Binding.qualify true (space_implode "_" new_type_names)
	      val b    = prfx (Binding.name "simps")
	      val pre_name  = Global_Theory.name_thms true true
	      val post_name = Global_Theory.name_thms false true
	      val naming    = Sign.naming_of T
              val name      = Name_Space.full_name naming b
              val thms2     = List.map Thm.derivation_name (post_name name (pre_name name (
                               (List.foldl (fn (i,l) => ((#inject i)@(#distinct i)@(#case_rewrites i)@l)) [] is)
                              @(#rec_rewrites info))))
	      (*
 cf. http://isabelle.in.tum.de/repos/isabelle/file/6d736d983d5c/src/HOL/Tools/Datatype/datatype_data.ML#l324
     http://isabelle.in.tum.de/repos/isabelle/file/6d736d983d5c/src/HOL/Tools/Datatype/datatype_data.ML#l340
*)
              val b1 = prfx (Binding.name "splits")
              val name1 = Name_Space.full_name naming b1
	      val splits = List.foldl (fn (i,l) => (#split i)::(#split_asm i)::l) [] is
              val thms3 = List.map Thm.derivation_name
                           (post_name name1 (pre_name name1 splits))
              (*
 cf. http://isabelle.in.tum.de/repos/isabelle/file/6d736d983d5c/src/HOL/Tools/Datatype/datatype_codegen.ML#l65
     http://isabelle.in.tum.de/repos/isabelle/file/6d736d983d5c/src/HOL/Tools/Datatype/datatype_codegen.ML#l109
      http://isabelle.in.tum.de/repos/isabelle/file/6d736d983d5c/src/HOL/Tools/Datatype/datatype_codegen.ML#l113
      http://isabelle.in.tum.de/repos/isabelle/file/6d736d983d5c/src/HOL/Tools/Datatype/datatype_codegen.ML#l114 *)
              fun eq_thms name =
                 let 
                  val (vs,cos) = Datatype.the_spec T (full_name T name);
                  val {descr, index, ... } = Datatype.the_info T (full_name T name);
                  val dummy = Skip_Proof.make_thm T (Var (("", 0), propT));
                  val triv_injects = map_filter
                    (fn (c,[]) => SOME (dummy)
                      | _ => NONE) cos;
                 val injects = map (fn _ => dummy) (nth (Datatype_Prop.make_injs [descr] vs) index);
                 val distincts = maps (fn _ => [dummy,dummy]) (snd (nth (Datatype_Prop.make_distincts [descr] vs) index));
                 val prefix = Binding.qualify true name o Binding.qualify true "eq" o Binding.name;
                 val name1 = Name_Space.full_name naming (prefix "refl");
                 val name2 = Name_Space.full_name naming (prefix "simps");
                 val thms = List.map Thm.derivation_name ((post_name name1 (pre_name name1 [dummy]))@(post_name name2 (pre_name name2 (triv_injects@injects@distincts))));
                in thms end
              val thms4 = flat (List.map eq_thms alt_names)
          in thms1@thms2@thms3@thms4 end
             fun check_rec (n,v) = if is_mutually_rec_type T (n,SOME(v))
                                    then if List.exists (fn altn => altn = n) (List.tl (Option.valOf (#alt_names v)))
                                          then false
                                         else true
                                   else true
             val ts' = List.foldl (fn (d,l) => case d of (n,SOME(v)) => if check_rec (n,v) then (n,v)::l
                                                                        else l
                                                       | (_,NONE) => l) [] ts
	 in unique (mergesort id (List.foldl (fn (t,l) => (get_ths t)@l) [] ts')) end
	fun filter rem d = remove' id #1 ((mergesort id rem),(mergesort #1 d))
end;
