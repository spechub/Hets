signature ExportHelper =
sig
	type const_info    = (string * (typ * term option)) list
        type term_info     = (string * term) list
        type datatype_info = (string * Datatype.info) list
        type def_info      = ((string * typ) * (indexname * typ) list *
         term) list
                             (* (name * type) * args@(argname * argtype) * 
                                def_term *)
        type fun_info      = (string * typ * (term list * term) list) list
                             (* name * type * def_eqs@(pats * def_term) *)
	type class_info	   = (string * (string list) * term_info *
         ((string * typ) list)) list
                             (* name * parents * assumes * fixes *)
        type locale_info   = (string * ((string * typ) * mixfix) list
                             (* name * fixes *)
                             * (string * term) list * (string * term) list
                             (* in-locale axioms    * ex-locale axioms *)
                             * string list) list
                             (* parents *) 
	type theory_info   = 
           string        (* theory name *)
         * string list   (* imports     *)
         * const_info    (* constants   *)
         * term_info     (* axioms      *)
         * term_info     (* theorems    *)
         * datatype_info (* data types  *)
         * def_info      (* definitions *)
         * fun_info      (* functions   *)
         * class_info    (* class info  *)
         * locale_info   (* locale info *)
        exception ExportError of string
        val theory_info : theory -> theory_info
        val tinfo2xml : theory -> string -> theory_info -> XML.tree
        val remove_parent_data : (theory -> 'a list) -> ('a -> string) -> theory -> 'a list
end;

structure ExportHelper : ExportHelper =
struct
(* Types *)
	type const_info    = (string * (typ * term option)) list
        type term_info     = (string * term) list
        type datatype_info = (string * Datatype.info) list
        type def_info      = ((string * typ) * (indexname * typ) list *
         term) list
                             (* (name * type) * args@(argname * argtype) * 
                                def_term *)
        type fun_info      = (string * typ * (term list * term) list) list
                             (* name * type * def_eqs@(pats * def_term) *)
	type class_info    = (string * (string list) * term_info *
         ((string * typ) list)) list
                             (* name * parents * assumes * fixes *)
	type locale_info   = (string * ((string * typ) * mixfix) list
                             (* name * fixes *)
                             * (string * term) list * (string * term) list
                             (* in-locale axioms    * ex-locale axioms *)
                             * string list) list
                             (* parents *)
	type theory_info   = 
           string        (* theory name *)
         * string list   (* imports     *)
         * const_info    (* constants   *)
         * term_info     (* axioms      *)
         * term_info     (* theorems    *)
         * datatype_info (* data types  *)
         * def_info      (* definitions *)
         * fun_info      (* functions   *)
         * class_info    (* class info  *)
         * locale_info   (* locale info *)
        exception ExportError of string

	structure XML_Syntax = Legacy_XML_Syntax

	fun all_locales T = Locale.pretty_locale_deps T

(* General helper functions *)
	fun internal_error s = raise (ExportError s)
	fun id x = x
	fun mergesort _ []  	   = []
	  | mergesort _ [x] 	   = [x]
	  | mergesort cmp_data xs  =
           let val (ys,zs) =
            List.foldl (fn(i, (ys,zs)) => (zs, i::ys)) ([],[]) xs
	     fun merge (xs,[]) = xs
	      | merge ([],xs) = xs
	      | merge (x::xr,y::yr) = if (cmp_data x) <= (cmp_data y)
		then x::merge(xr,y::yr)
	        else y::merge(x::xr,yr)
	   in merge(mergesort cmp_data ys, mergesort cmp_data zs) end
	(* remove duplicate entries from a sorted list *)
	fun unique [] 		= []
          | unique [x]		= [x]
          | unique (x1::x2::xr) = if x1 = x2
                                   then unique (x2::xr)
                                  else x1::(unique (x2::xr))
	(* remove xs from ys - both lists need to be sorted asc *)
	fun remove' _ _ ([],ys)           = ys
	  | remove' _ _ (_,[])		  = []
	  | remove' cd1 cd2 (x::xr,y::yr) =
             if (cd1 x) < (cd2 y)
	      then remove' cd1 cd2 (xr,y::yr)
	      else if (cd2 y) < (cd1 x)
	       then y::(remove' cd1 cd2 (x::xr,yr))
		else remove' cd1 cd2 (xr,yr)
	fun remove cmp_data = remove' cmp_data cmp_data
	fun remove_parent_data df cmp_data T =
         let val d  = df T
	     val pd = (List.foldl op@ [] (map df (Context.parents_of T)))
         in remove cmp_data (mergesort cmp_data pd,mergesort cmp_data d) end
        fun filterWith m (rem : string list) d =
         remove' id m ((mergesort id rem),(mergesort m d))
	fun filter rem (d : (string * 'a) list) =
         filterWith #1 rem d
(* Theory-specific helpers *)
        (* remove unnecessary information from (recursive) datatypes *)
	fun is_mutually_rec_type (_,i) = length (#descr i) > 1
	fun check_rec (n,v) = if is_mutually_rec_type (n,v)
         then (#index v) < 1
         else true
        fun restructure_rec_types ts = List.foldl (fn (d,l) => case d of
         (n,SOME(v)) => if check_rec (n,v) then (n,v)::l
                        else l
         | (_,NONE) => l) [] ts
        fun unfold_conjunction tm =
         case tm of
            (Const ("Pure.conjunction",_)) $ t => unfold_conjunction t
          | t $ (Const ("Pure.conjunction",_)) => unfold_conjunction t
          | t1 $ t2                            =>
             (unfold_conjunction t1)
            @(unfold_conjunction t2)
          | _                                  => [tm]
        fun unfold_hol_conjunction tm = case tm of
	   Const ("HOL.conj",_) $ t $ t1 => (unfold_hol_conjunction t)@(unfold_hol_conjunction t1)
         | Const ("HOL.conj",_) $ t => [t]
         | _ => [tm]
	fun strip_hol_all l b tm = case (b,tm) of
           (true,Const ("HOL.All",_) $ Abs (s,t,tm)) =>
            strip_hol_all ((s,t)::l) true tm
         | (_,Bound i) => if List.length l > i
                          then let val (s,t) = List.nth(l,i)
                               in Var ((s,0),t) end
                          else tm
         | (_,Abs (s,t,tm)) => Abs (s,t,strip_hol_all l false tm)
         | (_,t1 $ t2) => (strip_hol_all l false t1) $ 
                          (strip_hol_all l false t2)
	 | _ => tm
	fun remove_hol_true_prop t = case t of
           op$ (Const ("HOL.Trueprop",_), tm) => tm
         | (t $ u) => (remove_hol_true_prop t) $ (remove_hol_true_prop u)
         | Abs (s,T,t) => Abs (s,T,remove_hol_true_prop t)
         | tm => tm

(* get raw theory information *)
	fun get_consts T =
         let val consts_of = (Name_Space.dest_table (Syntax.init_pretty_global T)) o
                             #constants o Consts.dest o Sign.consts_of
         in remove_parent_data consts_of #1 T end
	val get_axioms = remove_parent_data Theory.axioms_of #1
	val get_theorems =
         let fun theorems_of T =  map (fn (a,b) => (a, prop_of b))
              (Global_Theory.all_thms_of T)
         in remove_parent_data theorems_of #1 end
	fun get_datatypes T =
         let val tname = Context.theory_name T
             val tl = String.size tname
             val ts = (#log_types o Type.rep_tsig o Sign.tsig_of) T
             val ts' = map (fn s => (String.extract (s,tl+1,NONE),Datatype.get_info T s))
                  (List.filter (String.isPrefix tname) ts)
         in restructure_rec_types ts' end
        fun get_def t =
         let val rec type_of_def = fn sig_def => case sig_def of
                      (Const (name,tp) $ _) => (name,tp)
                    | v $ _ => type_of_def v
                    | _ => internal_error "ExportHelper.get_def - Failed to parse variables!";
             val rec vars_of_def = fn sig_def => case sig_def of
                      vs $ (Var (name,tp)) => (name,tp) :: (vars_of_def vs)
                    | _ => []
         in case t of
            (Const ("==",_) $ sig_def $ def) =>
             (type_of_def sig_def,List.rev (vars_of_def sig_def),def)
          | _ => internal_error "ExportHelper.get_def - Failed to parse definition!" end
        fun get_defs thms =
         let val def_suffix = "_def"
             val defs       = List.map (fn (_,tm) => get_def tm) (List.filter
              (fn (n,_) => String.isSuffix def_suffix n) thms)
         in defs end
        fun fun_def c =
         let val rec pats_of = fn pats => case pats of
                      ps $ p => p :: (pats_of ps)
                    | _ => []
         in case prop_of c of Const ("==>",_) $ _ $ (Const ("HOL.Trueprop",_)
             $ (Const ("HOL.eq",_) $ pats $ def)) =>
              (List.rev (pats_of pats),def)
            | _ => internal_error "ExportHelper.fun_def - Failed to parse equation" end
        fun get_funs T =
          let val funs_of = fn T => 
            let val d = Item_Net.content (Function_Common.get_function
                     (Proof_Context.init_global T))
            in List.map (fn (c,i) => case c of Const (n,t)
                          => (n,t,((List.map fun_def) o #psimps) i)
                         | _ => internal_error "ExportHelper.get_funs - failed to parse function name") d end
          in remove_parent_data funs_of #1 T end
	fun get_classes T thms = 
         let val cls_suffix = "_class_def"
             val cls_names = List.map (fn n => String.substring
              (n,0,String.size n-String.size cls_suffix))
              (List.filter (fn n =>
               if String.isSuffix cls_suffix n
               then true else false) (List.map #1 thms))
         in List.map (fn name =>
          let val name' = String.substring (name,String.size "Class.",
                       String.size name - String.size "Class.")
	      val i = AxClass.get_info T name
              val parents = let fun split tms = case tms of
                             (Const ("HOL.Trueprop",_))::_ => []
                           | (Const ("TYPE",_))::tms' => (split tms')
                           | (Const (s,_))::tms' => let val s' = 
                              if String.isPrefix "Class." s
                              then String.substring (s,String.size "Class.",
                                    String.size s - String.size "Class."
                                     - String.size "_class")
                               else s
                              in s'::(split tms') end
                           | _::tms' => (split tms')
                           | [] => []
               in case (Thm.prop_of o #def) i of
                     _ $ t => (split o unfold_conjunction) t
                   | _ => [] end
              val axioms' = List.filter
               (fn (n,_) => String.isPrefix (name^".") n) thms
              val axioms = List.map (fn (n,t) => case t of
                 _ $ (_ $ t') => (n,t')
               | _ => (n,t)) axioms'
              val params = #params i
          in (name',parents,axioms,params) end) cls_names end
        fun fix_consts' params t = case t of
          Var ((s,_),_) => (case List.find (fn ((s',_),_) => s'=s) params of
                             SOME ((s,tp),_) => Const (s,tp)
                           | NONE => t)
         | Abs (s,tp,tm) => Abs (s,tp,fix_consts' params tm)
         | t1 $ t2 => (fix_consts' params t1) $ (fix_consts' params t2)
         | _ => t
        fun fix_consts params ts = List.map (fn (s,t) =>
         (s,fix_consts' params t)) ts
	fun get_locales T thms = 
         let val cls_suffix = "_class_def"
             val cls_names = List.map (fn n => String.substring
              (n,0,String.size n-String.size cls_suffix))
              (List.filter (fn n =>
               if String.isSuffix cls_suffix n
               then true else false) (List.map #1 thms))
             val names' = List.filter ((String.isPrefix
                           (Context.theory_name T)) o #1)
                           (List.map (fn l => (#name l,#parents l))
                            (all_locales T))
             val names = List.filter ((fn s =>
               not (List.exists (fn s' => s = s') cls_names)) o #1) names'
             val filter = ["_axioms.intro","_axioms_def",
              "_def",".intro",".axioms_"]
         in List.map (fn (name,ps) => 
           let val params'   = Locale.params_of T name
               val params    = List.filter (fn ((s,_),_) =>
                   not (List.exists (fn p => p = s) ps)) params'
               val axs       = List.filter (fn t => String.isPrefix name (#1 t))
                                (Global_Theory.all_thms_of T)
               val axioms'  = List.filter
                    (fn t => (not (List.exists
                              (fn s => String.isPrefix (name ^ s) (#1 t))
                             filter))) axs
               val axioms   = List.map (fn (s,t) =>
                    (s,(remove_hol_true_prop o
                      (fn Const ("==>",_) $ _ $ t => t
                         | _ => internal_error
 ("ExportHelper.get_locales - Failed to parse axioms for locale "^name)) o Thm.prop_of) t))
                    axioms'
               val in_locale_axioms =
                case (List.find (fn x => (#1 x) = (name^"_axioms_def")) axs) of
                   SOME v => List.map (strip_hol_all [] true)
                  ((unfold_hol_conjunction o
                   (fn _ $ _ $ tm => tm
                      |_ => internal_error
 ("ExportHelper.get_locales - Failed to parse axioms definition for locale "^name)) o Thm.prop_of o #2) v)
                 | _ => case (List.find (fn x => (#1 x) = (name^"_def")) axs) of
                         SOME v => List.map (strip_hol_all [] true)
                          ((unfold_hol_conjunction o
                           (fn _ $ _ $ tm => tm
                              |_ => internal_error
 ("ExportHelper.get_locales - Failed to parse axioms definition for locale "^name)) o Thm.prop_of o #2) v)
                       | _ => []
               val in_loc = List.filter (fn (_,t) => 
                    List.exists (fn t' => t = t') in_locale_axioms) axioms
               val ex_loc = List.filter (fn (_,t) => 
                    not (List.exists (fn t' => t = t') in_locale_axioms)) axioms
           in (name,params,fix_consts params' in_loc,fix_consts params' ex_loc,ps) end
          ) names end
(* Guess the names of generated axioms, consts and theorem *)
        fun prefix p s = List.map (fn x => p^s^x)
        fun postfix s p = List.map (fn x => x^s^p)
        fun l_to_intl l = List.map Int.toString 
         (List.tl (List.rev (List.foldl 
           (fn (_,x::xs) => (x+1)::x::xs
              |_ => internal_error
 "ExportHelper.l_to_intl - Unexpected condition") [0] l)))
	fun get_type_names ts =
            let
	     val rec_types = List.filter check_rec ts
	     val grouped_rec_names = List.map (fn x => 
                   List.map (Long_Name.base_name o #1 o #2) ((#descr o #2) x)) rec_types
  	     val def_names = (List.map (Long_Name.base_name o #1 o #2) 
                              (List.concat (List.map (#descr o #2) rec_types)))
	     val all_rec_names = (List.concat grouped_rec_names)@def_names
	     val constructors = List.map #1 (List.concat (List.map (#3 o #2) 
                                 (List.concat (List.map (#descr o #2) ts))))
            in (grouped_rec_names,all_rec_names,constructors,def_names) end
	fun get_gen_consts T name ts consts funs =
         let val (grouped_rec_names,all_rec_names,constructors,_) = get_type_names ts
	     val rec_names = List.concat grouped_rec_names
	     val mutually_rec_names =
                  List.filter (fn x => List.length x > 1) grouped_rec_names
	     val simple_names = List.map List.hd
                  (List.filter (fn x => List.length x = 1) grouped_rec_names)
             val locale_names = List.filter
                  (String.isPrefix (Context.theory_name T))
                  (List.map #name (all_locales T))
         in constructors@(prefix name "." (List.concat
             [prefix "Abs" "_" rec_names,
              prefix "Rep" "_" rec_names,
              List.map (fn x => "equal_"^x^"_inst.equal_"^x) all_rec_names,
              List.concat (List.map (fn x => let val comb = space_implode "_" x
               in (List.map (fn y => comb^"."^y^"_case") x) end) grouped_rec_names),
              List.concat (List.map (fn x => [x^"."^x^"_rec",
				 x^"."^x^"_rec_set",
				 x^"."^x^"_rep_set"]) simple_names),
              List.concat (List.map
               (fn x => let val comb = space_implode "_" x
                        in (comb^"."^comb^"_rec_set")::
                           (comb^"."^comb^"_rep_set")::(List.concat
                            (List.map 
                             (fn y => [comb^"."^comb^"_rec_"^y,
                                       comb^"."^comb^"_rec_set_"^y,
                                       comb^"."^comb^"_rep_set_"^y])
                             (l_to_intl x))) end) mutually_rec_names)]))
            @(List.filter (String.isPrefix "Class.") consts)
            @(List.filter (fn s => List.exists
              (fn l => String.isPrefix l s) locale_names) consts)
            @(postfix "_" "graph" funs)
            @(postfix "_" "rel" funs)
            @(postfix "_" "dom" funs)
            @(postfix "_" "sumC" funs)
            @funs end
	fun get_gen_axioms name ts =
         let val (grouped_rec_names,_,constructors,def_names) =
                  get_type_names ts
             val rec_names = List.concat grouped_rec_names
             val mutually_rec_names = List.filter (fn x => List.length x > 1)
                  grouped_rec_names
             val simple_names = List.map List.hd
                  (List.filter (fn x => List.length x = 1) grouped_rec_names)
         in (postfix "_" "def" constructors)@(prefix name "." (List.concat 
             [prefix "arity_type" "_" def_names,
              prefix "equal" "_" (postfix "_" "def_raw" def_names),
	      prefix "type_definition" "_" rec_names,
	      List.map (fn x => "equal_"^x^"_inst.equal_"^x^"_def") def_names,
	      (postfix "_" "def"
               (List.concat [(List.concat (List.map
                (fn x => let val comb = space_implode "_" x
                         in (comb^"."^comb^"_rec_set")::
                            (comb^"."^comb^"_rep_set")::(List.concat
                             (List.map
                               (fn y => [comb^"."^comb^"_rec_"^y,
                                 comb^"."^comb^"_rec_set_"^y,
                                 comb^"."^comb^"_rep_set_"^y]) (l_to_intl x))) end)
                   mutually_rec_names)),
                List.concat (List.map (fn x => let val comb = space_implode "_" x
                 in (List.map (fn y => comb^"."^y^"_case") x) end) grouped_rec_names),
                List.concat (List.map (fn x => [x^"."^x^"_rec",
                                                x^"."^x^"_rec_set",
                                                x^"."^x^"_rep_set"]) simple_names)]))])) end
	fun get_gen_theorems T name ts ths funs =
         let val (grouped_rec_names,_,_,def_names) =
                  get_type_names ts
             val rec_names = List.concat grouped_rec_names
             val mutually_rec_names = List.filter (fn x => List.length x > 1)
                  grouped_rec_names
             val locale_names = List.filter
                  (String.isPrefix (Context.theory_name T))
                  (List.map #name (all_locales T))
	     val locale_filter = ["_axioms.intro","_axioms_def","_def","."]
         in prefix name "." (List.concat
          [prefix "arity_equal" "_" def_names,
           prefix "arity_type" "_" def_names,
	   prefix "type_definition" "_" rec_names,
	   prefix "equal" "_" (postfix "_" "def" def_names),
           prefix "equal" "_" (postfix "_" "def_raw" def_names),
	   List.map (fn x => "equal_"^x^"_inst.equal_"^x) def_names])
         @postfix "_" "def" (List.concat
          [postfix "_" "rel" funs,
           postfix "_" "sumC" funs,
           postfix "_" "graph" funs,
           funs])
         @(List.concat (List.map (fn x =>
            List.filter (String.isPrefix (name^"."^x^".")) ths) (unique (rec_names@def_names))))
         @(List.concat (List.map (fn x =>
            List.filter (String.isPrefix (name^"."^(space_implode "_" x)^".")) ths)
           mutually_rec_names))
         @(List.filter (String.isPrefix "Class.") ths)
         @(List.concat (List.map (fn f => List.filter
          (String.isPrefix f) ths) funs))
         @(List.filter (fn s => (List.exists 
           (fn l => List.exists
           (fn f => String.isPrefix (l^f) s) locale_filter) locale_names)) ths)
end
(* Represent collected data as XML *)
	(* Enrich the (isabelle-builtin) XML representation of terms with infix information *)
        fun mixfix_to_args m = case m of
                     SOME(Mixfix.Infixl (s,j)) =>
                       [("infixl",s),
                        ("mixfix_i",string_of_int j)]
                   | SOME(Mixfix.Infixr (s,j)) =>
                       [("infixr",s),
                        ("mixfix_i",string_of_int j)]
                   | SOME(Mixfix.Infix (s,j))  =>
                       [("infix",s),
                        ("mixifix_i",string_of_int j)]
                   | _ => []
        fun xml_of_term' T tbl t =
          case t of
           XML.Elem (("Const",a),t) =>
              let val b = case (Syntax.guess_infix (Sign.syn_of T)
                 (Lexicon.mark_const ((#2 o List.hd) a))) of
                  SOME(mx) => mixfix_to_args (SOME mx)
                 |NONE => mixfix_to_args (Symtab.lookup tbl ((#2 o List.hd) a))
              in XML.Elem (("Const",a@b),map (xml_of_term' T tbl) t) end
           | XML.Elem ((s,a),t) => XML.Elem ((s,a),map (xml_of_term' T tbl) t)
           | _ => t
        fun xml_of_term T t = xml_of_term' T Symtab.empty
             (XML_Syntax.xml_of_term t)
	fun termListToXML T section l = XML.Elem ((section,[]),List.map (
         fn (s,t) => XML.Elem (("Term",[("name",Long_Name.base_name s)]),
                      [xml_of_term T (remove_hol_true_prop t)])) l)
	fun termTypListToXML T section l = XML.Elem ((section,[]),List.map (
	 fn (s,(t,v)) => let val v' = case v of
          SOME(tm) => (("Term",[("name",Long_Name.base_name s)]),[xml_of_term T tm])
	  | NONE => (("NoTerm",[]),[])
         in XML.Elem (("ConstDecl",[("name",Long_Name.base_name s)]),
             [XML_Syntax.xml_of_type t,XML.Elem v']) end) l)
	fun dtypToXML (Datatype.DtTFree (s,_)) = XML.Elem (("DtTFree",[("s",s)]),[])
           | dtypToXML (Datatype.DtType (s,dtl)) =
              XML.Elem (("DtType",[("s",s)]),List.map dtypToXML dtl)
    	   | dtypToXML (Datatype.DtRec i) =
              XML.Elem (("DtRec",[("i",Int.toString i)]),[])
	fun constructorToXML (name,dtl) = XML.Elem
         (("Constructor",[("val",Long_Name.base_name name)]),List.map dtypToXML dtl)
	fun typeToXML d = List.map
         (fn (i,(s,vs,dt)) => let val attrs = 
              [("i",Int.toString i),("name",Long_Name.base_name s)]
          in XML.Elem (("RecType",attrs),[
               XML.Elem (("Vars",[]),List.map dtypToXML vs),
	       XML.Elem (("Constructors",[]),List.map constructorToXML dt)
              ])
          end)
         (#descr d)
	fun typeListToXML section l = XML.Elem ((section,[]),List.map (
	 fn (s,d) => XML.Elem (("TypeDecl",[("name",s)]),typeToXML d)) l)
(* Prepare data *)
	(* make sure that type names local to the theory do not
           have the theory name as prefix
           (because this is not their proper name) *)
        fun fixTypeNames moduleName t = case t of
             XML.Elem (("Type",a),c) => XML.Elem (("Type",
                List.map (fn (n,s) =>
                 if n = "name" andalso String.isPrefix (moduleName^".") s
                  then (n,String.extract (s,(String.size moduleName)+1,NONE))
                  else (n,s)) a),
                List.map (fixTypeNames moduleName) c)
             | XML.Elem (d,c) =>
                XML.Elem (d,List.map (fixTypeNames moduleName) c)
             | _ => t
(* Module interface *)
	(* collect information necessary to reconstruct the theory *)
	fun theory_info T =
         let val name       = Context.theory_name T
             val imports    = List.map
              Context.theory_name (Theory.parents_of T)
             val types      = get_datatypes T
             val consts     = get_consts T
             val thms       = get_theorems T
             val axioms     = get_axioms T
	     val classes    = get_classes T thms
             val funs       = get_funs T
             val gen_consts'= get_gen_consts T name types (List.map #1 consts)
                               (List.map #1 funs)
             val gen_thms'  = get_gen_theorems T name types (List.map #1 thms)
                               (List.map #1 funs)
             val defs       = get_defs (filter gen_thms' thms)
             val def_names  = List.map (#1 o #1) defs
             val funs       = get_funs T
             val gen_consts = def_names@gen_consts'
             val gen_thms   = (postfix "_" "def" def_names)@gen_thms'
             val gen_axioms = (get_gen_axioms name types)@(List.map #1 thms)
                              @(postfix "_" "def_raw" def_names)
             val locales    = get_locales T thms
         in (name, imports,
             (filter gen_consts consts),
             (filter gen_axioms axioms),
             (filter gen_thms thms),
             types,defs,funs,classes,locales) end
	(* export theory info as xml *)
	fun tinfo2xml T fname (name,imports,consts,axioms,thms,
                                types,defs,funs,classes,locales) =
         let val b = Long_Name.base_name
             val xml_imports  = XML.Elem
              (("Imports",[]), List.map (fn s => XML.Elem (("Import",[("name",s)]),[])) imports)
             val xml_consts   = termTypListToXML T "Consts" consts
             val xml_axioms   = termListToXML T "Axioms" axioms
             val xml_theorems = termListToXML T "Theorems" thms
             val xml_types    = typeListToXML "Types" types
             val xml_defs     = XML.Elem (("Defs",[]), List.map
              (fn ((name,tp),args,tm) => XML.Elem (("Def",
               [("name",Long_Name.base_name name)]),
                [XML_Syntax.xml_of_type tp]
                @(List.map (fn ((n,_),t) => XML.Elem (("Arg",[("name",n)]), 
                  [XML_Syntax.xml_of_type t])) args)
                @[xml_of_term T tm])) defs)
             val xml_funs     = XML.Elem (("Funs",[]),List.map
              (fn (name,tp,def_eqs) => XML.Elem (("FunDef",
               [("name",Long_Name.base_name name)]),
                [XML_Syntax.xml_of_type tp]@List.map
               (fn (pats,def) => XML.Elem (("FunDefEq",[]),
                [xml_of_term T def]
               @(List.map (xml_of_term T) pats))) def_eqs)) funs)
             val xml_classes  = XML.Elem (("Classes",[]),List.map
              (fn (name,parents,axioms,params) =>
                XML.Elem (("ClassDecl",[("name",name)]),
                (List.map (fn (s,t) => XML.Elem 
                 (("Axiom",[("name",Long_Name.base_name s)]),
                 [xml_of_term T (remove_hol_true_prop t)])) axioms)
               @((List.map (fn (s,t) => XML.Elem 
                 (("Param",[("name",Long_Name.base_name s)]),
                 [XML_Syntax.xml_of_type t])) params))
               @(List.map (fn n => XML.Elem
                 (("Parent",[("name",n)]),[])) parents))) classes)
             val xml_locales  = XML.Elem (("Locales",[]),List.map
                  (fn (name,params,in_loc,ex_loc,parents) =>
                  let val tbl = List.foldl (fn (((s,_),m),t) => 
                             Symtab.update (s,m) t)
                            Symtab.empty (Locale.params_of T name) in
                    XML.Elem (("LocaleDecl",[("name",b name)]),
                     (List.map (fn ((s,t),m) =>
                       XML.Elem (("LocaleParam",[("name",s)]
                         @(mixfix_to_args (SOME m))),
                       [XML_Syntax.xml_of_type t])) params)
                    @(List.map (fn (s,t) => XML.Elem
                        (("IAxiom",[("name",b s)]),
                         [xml_of_term' T tbl (XML_Syntax.xml_of_term t)]))
                      in_loc)
                    @(List.map (fn (s,t) => XML.Elem
                        (("EAxiom",[("name",b s)]),
                         [xml_of_term' T tbl (XML_Syntax.xml_of_term t)]))
                      ex_loc)
                    @(List.map (fn n => XML.Elem
                      (("Parent",[("name",b n)]),[])) parents)
                    )end) locales)
         in fixTypeNames name (XML.Elem (("IsaExport",[("file",fname)]),
             [xml_imports,xml_consts,xml_axioms,xml_theorems,xml_types,xml_defs,xml_funs,xml_classes,xml_locales])) end
end;
