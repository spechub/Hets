signature ExportHelper =
sig
	(* types *)
        type named_term = (string * term)
        (* general helper functions *)
        val unlines          : string list -> string
        val unqualify        : string -> string
        (* isabelle specific functions *)
	val theory_of_string : string -> theory list -> theory
        val theory_by_name   : string -> theory
        val name_of_theory   : theory -> string
        val axioms_of        : theory -> named_term list
	val non_image_theories : theory -> theory list
        val thms_of          : theory -> named_term list
        val consts_of        : theory -> (string * typ) list
	val datatypes_of     : theory -> ((string * typ list *
                                          (string * typ list) list) list) list
                          (* mutually_rec_types@(name * type_params *
                             constructors@(constructor_name * type_args))) *)
	val functions_of     : theory -> (string * typ *
                                          (term list * term) list) list
                                         (* name * type *
                                            def_eqs@(pats * defterm) *)
        val classes_of       : theory -> (class * string list *
                                          (string * term) list *
                                          (string * typ) list) list
                                         (* name * parents * assumes * fixes *)
        val locales_of       : theory -> (string *
                                          ((string * typ) * mixfix) list *
                                          named_term list * named_term list *
                                          string list) list
                                         (* name * fixes * in-locale axioms *
                                            ex-locale axioms * parents *)
	val pretty_as_str    : Pretty.T -> string
	val repr_term        : theory -> term -> Pretty.T
        val repr_typ         : theory -> typ -> Pretty.T
	val repr_name        : string -> Pretty.T
        val repr_function    : theory -> (string * typ *
                                          (term list * term) list) -> Pretty.T
	val repr_class       : theory -> (class * string list *
                                          (string * term) list *
                                          (string * typ) list) -> Pretty.T
	val repr_locale      : theory -> (string *
                                          ((string * typ) * mixfix) list *
                                          named_term list * named_term list *
                                          string list) -> Pretty.T
	val repr_datatype    : theory -> (string * typ list * (string *
                                          typ list) list) list -> Pretty.T
	val theory_of_exportable_data : theory -> theory
        val get_basic_theory_data     : theory -> (named_term list *
                                                   named_term list *
                                                   (string * typ) list)
                                        (* axioms * theorems * consts *)
        type theory_data = (string * named_term list * named_term list *
                            (string * typ) list * ((string * typ list *
                             (string * typ list) list) list) list *
                            (string * typ * (term list * term) list) list *
                            (class * string list * (string * term) list *
                             (string * typ) list) list *
                            (string * ((string * typ) * mixfix) list *
                              named_term list * named_term list *
                              string list) list)
                           (* name * axioms * theorems * consts * datatypes *
                              functions * classes * locales *)
        val get_theories    : theory -> theory_data list
        val xml_of_theories : theory_data list -> XML.tree
        exception ExportError of string
end;

structure ExportHelper : ExportHelper =
struct

exception ExportError of string

type named_term = string * term

type theory_data = (string * named_term list * named_term list *
                            (string * typ) list * ((string * typ list *
                             (string * typ list) list) list) list *
                            (string * typ * (term list * term) list) list *
                            (class * string list * (string * term) list *
                             (string * typ) list) list *
                            (string * ((string * typ) * mixfix) list *
                              named_term list * named_term list *
                              string list) list)
                           (* name * axioms * theorems * consts * datatypes * 
                              functions * classes * locales *)

(* ------------------------------ General helper functions    *)

val unlines    = String.concatWith (String.str (Char.chr 10))

fun lift f sel = fn (t1,t2) => f (sel t1,sel t2)

fun unqualify n = if Long_Name.is_qualified n
                  then (Long_Name.implode (List.tl (Long_Name.explode n)))
                  else n

(* ------------------------------ Isabelle specific functions *)

(* Keep track of the number of theories created from a string  *)
val thmNum = Unsynchronized.ref 0

(* create a theory from a string of its body *)
fun theory_of_string body parents =
     let val name   = "TempTheory"^Int.toString (Unsynchronized.inc thmNum)
         val header = Thy_Header.make ("TempTheory",Position.none) [] [] []
         val text   = unlines ["theory "^name,"begin",body,"end"]
     in #1 (Thy_Load.load_thy 0 (Thy_Load.get_master_path ()) header
         Position.start text parents) end

fun remove_hol_true_prop t = case t of
   op$ (Const ("HOL.Trueprop",_), tm) => tm
 | (t $ u) => (remove_hol_true_prop t) $ (remove_hol_true_prop u)
 | Abs (s,T,t) => Abs (s,T,remove_hol_true_prop t)
 | tm => tm

val prettify_term = Logic.strip_imp_concl o remove_hol_true_prop

(* remove data that is already present in a parent theory *)
fun remove_parent_data df cmp T =
 let val d = df T
     val pd = (List.foldl op@ [] (List.map df (Context.parents_of T)))
 in Ord_List.subtract cmp (Ord_List.make cmp pd) (Ord_List.make cmp d) end

(* a couple of aliases *)
val theory_by_name = Thy_Info.get_theory
val name_of_theory = Context.theory_name
val axioms_of      = Theory.axioms_of

(* check if the theory is not part of the logic image *)
fun is_non_image_theory T = length (Thy_Info.loaded_files (name_of_theory T)) > 0

fun non_image_theories T = List.concat (List.map
     (fn T' => if is_non_image_theory T'
               then T'::(non_image_theories T') else [])
     (Context.parents_of T))

fun hol_forall_elim tm =
 let val qnt  = #1 (Term.dest_Const (HOLogic.all_const HOLogic.boolT))
     val body = Term.strip_qnt_body qnt tm
     val vars = List.map (fn (s,tp) => Var ((s,0),tp))
                 (Term.strip_qnt_vars qnt tm)
 in Term.subst_bounds (List.rev vars, body) end

fun hol_conjunctions tm = case HOLogic.dest_conj tm of
   [_] => [tm]
 | tms => List.concat (List.map hol_conjunctions tms)

fun thms_of T      = List.map (fn (s,d) => (s,prop_of d))
                      (remove_parent_data Global_Theory.all_thms_of
                      (lift fast_string_ord #1) T)

(* currently there seems to be no way (anymore) to
   attach any terms to a const directly. Thus the discarded
   part is (hopefully) always NONE
   todo: maybe throw an exception if this is not the case? *)
fun consts_of T    =
 let val get_consts = fn T => List.map (fn (n,(t,_)) => (n,t))
                       (((Name_Space.dest_table (Syntax.init_pretty_global T)) o
                        #constants o Consts.dest o Sign.consts_of) T)
 in remove_parent_data get_consts (lift fast_string_ord #1) T end

fun datatypes_of T =
 let val get_datatypes = (#log_types o Type.rep_tsig o Sign.tsig_of)
     val ts            = remove_parent_data get_datatypes fast_string_ord T
     val is_mutually_rec_type  = fn (_,i) => length (#descr i) >1
     val check_rec             = fn (n,v) => if is_mutually_rec_type (n,v)
                                  then (#index v) < 1 else true
     val rec dtyp2typ = fn (descs,t) => case t of
            Datatype.DtTFree (s,srt) => TFree (s,srt)
          | Datatype.DtType (s,ts)   =>
             Type (s,List.map (curry dtyp2typ descs) ts)
          | Datatype.DtRec i         =>
             case List.find (curry op= i o #1) descs of
               SOME (_,(s,ts,_)) => Type (s, List.map
                (curry dtyp2typ descs) ts)
             | NONE => raise ExportError("Internal Error!")
     val dt_desc = fn info => List.map (fn (i,(s,vs,eqs)) =>
      let val vs'  = List.map (curry dtyp2typ info) vs
          val eqs' = List.map (fn (s,ts) =>
                      (s,List.map (curry dtyp2typ info) ts)) eqs
      in (s,vs',eqs') end) info
 in List.foldl (fn (n,l) => case Datatype.get_info T n of
                             SOME(v) => if check_rec (n,v)
                                        then (dt_desc (#descr v))::l
                                        else l
                           | NONE    => l) [] ts end

(* Notes:
   HOLogic    is in HOL/Tools/hologic.ML
   dest_Const is in Pure/term.ML
   Logic      is in Pure/logic.ML *)

val functions_of =
 let val get_funs = fn T =>
  let val d = Item_Net.content (Function_Common.get_function
               (Proof_Context.init_global T))
      val fun_def = (fn (pats,def) => (#2 (strip_comb pats),def))
                     o HOLogic.dest_eq o HOLogic.dest_Trueprop o #2
                     o Logic.dest_implies o prop_of
  in List.map (fn (c,i) => case dest_Const c of
      (n,t) => (n,t,List.map fun_def (#psimps i))) d end
 in remove_parent_data get_funs (lift fast_string_ord #1) end

fun classes_of T =
 let val cls_suffix = "_class_def"
     val thms       = thms_of T
     val cls_names  = List.map (fn n => String.substring (n,0,String.size n-
          String.size cls_suffix)) (List.filter (String.isSuffix cls_suffix)
          (List.map #1 thms))
 in List.map (fn name => 
     let val i        = AxClass.get_info T name
         val parents' = List.concat (List.map
             (fn tm => Term.add_const_names tm [])
             ((Logic.dest_conjunction_list o #2
           o Logic.dest_equals o Thm.prop_of o #def) i))
         val parents  = List.map (fn n => String.substring
              (n,0,String.size n - String.size "_class"))
              (List.filter (fn n => (String.isSuffix "_class" n) andalso
              (not (String.isPrefix "HOL" n))) parents')
         val axioms'  = List.map (fn (n,t) => (n,(HOLogic.dest_Trueprop o #2
           o Logic.dest_implies) t))
          (List.filter ((String.isPrefix (name^".")) o #1) thms)
         (* note: instead of cls_names we should only use
                  ancestors of the class *)
         val all_params = List.map (fn (s,t) => (Long_Name.base_name s,t))
              (List.concat (List.map (#params o AxClass.get_info T) cls_names))
         val sub_vars   = List.map (fn (s,t) => ((s,0),Free (s,t))) all_params
         val axioms     = List.map (fn (s,t) => (s,Term.subst_Vars sub_vars t))
                           axioms'
     in (name,parents,axioms,#params i) end) cls_names end

fun locales_of T   =
 let val all_locales   = fn T => List.map (fn l => (#name l,  #parents l))
                                  (Locale.pretty_locale_deps T)
     val locales       = Ord_List.subtract
                          (fn (c,l) => fast_string_ord (#1 c,#1 l))
                          (Ord_List.make (lift fast_string_ord #1)
                                         (classes_of T))
                          (Ord_List.make (lift fast_string_ord #1)
                            (remove_parent_data all_locales
                             (lift fast_string_ord #1) T))
 in List.map (fn (name,ps) =>
   let val parent_params = List.map (#1 o #1) (List.concat
            (List.map (Locale.params_of T o #1)
            (List.filter (fn (s,_) => List.exists (curry op= s) ps) locales)))
       val params  = Ord_List.subtract (fn (s,((s1,_),_)) =>
                                         fast_string_ord (s,s1))
                      (Ord_List.make fast_string_ord parent_params)
                      (Ord_List.make (lift fast_string_ord (#1 o #1))
                                     (Locale.params_of T name))
       val filter  = ["_axioms.intro","_axioms_def","_def",".intro",".axioms_"]
       val axs     = List.filter ((String.isPrefix name) o #1)
                                 (Global_Theory.all_thms_of T)
       val axioms' = List.filter
            (fn t => (not (List.exists
                      (fn s => String.isPrefix (name ^ s) (#1 t))
                     filter))) axs
       val axioms  = List.map (fn (s,t) => (s,(HOLogic.dest_Trueprop o #2
                                           o Logic.dest_implies
                                           o Thm.prop_of) t)) axioms'
       val fix_consts       = List.map (fn (s,t) => (s, Term.subst_Vars
                                          (List.map (fn ((s,tp),_) => 
                                          ((s,0),Const (s,tp))) params) t))
       val parse_axioms     = fn v => List.map hol_forall_elim
            ((hol_conjunctions o #2 o Logic.dest_equals o Thm.prop_of o #2) v)
       val in_locale_axioms =
          case List.find ((curry op= (name^"_axioms_def")) o #1) axs of
             SOME v => parse_axioms v
           | _      =>
             case List.find ((curry op= (name^"_def")) o #1) axs of
                SOME v => parse_axioms v
              | _      => []
       val in_loc = List.filter (fn (_,t) =>
            List.exists (fn t' => t = t') in_locale_axioms) axioms
       val ex_loc = List.filter (fn (_,t) =>
            not (List.exists (fn t' => t = t') in_locale_axioms)) axioms
   in (name,params,fix_consts in_loc,fix_consts ex_loc,ps) end) locales end

(* ------------------------------ Represent as string *)

fun pretty_as_str p = Pretty.str_of p

fun repr_term T =
 let val ctxt = Config.put Printer.show_question_marks false
          (Proof_Context.init_global T)
 in Syntax.pretty_term ctxt end

fun repr_typ T  = Syntax.pretty_typ  (Proof_Context.init_global T)

fun repr_name n' =
 let val n = Long_Name.base_name n'
 in if String.isSubstring " " n then Pretty.quote (Pretty.str n)
    else Pretty.str n end

fun repr_function T (s,tp,def_eqs) =
 let val head = [Pretty.str "fun ", repr_name s, Pretty.str " :: ",
                 Pretty.quote (repr_typ T tp), Pretty.str " where "]
     val body = List.map (fn (pats,tm) => Pretty.quote (Pretty.block
                 ((Pretty.breaks ([repr_name s]
                    @(List.map (fn p => Pretty.enclose "(" ")" [repr_term T p])
                                         pats)))@
                  [Pretty.str " = ",repr_term T tm]))) def_eqs
 in Pretty.block (head@Pretty.separate " | " body) end

fun repr_class T (s,ps,assumes,fixes) =
 let val head     = [Pretty.str "class", repr_name s]
                    @(if length fixes + length assumes + length ps > 0
                      then [Pretty.str "="] else [])
     val parents  = List.map repr_name ps
     val fixes'   = List.map (fn (s,tp) => Pretty.block (Pretty.breaks
                     [repr_name s,Pretty.str "::",
                      Pretty.quote (repr_typ T tp)])) fixes
     val assumes' = List.map (fn (s,tm) => Pretty.block (Pretty.breaks
                     [repr_name s, Pretty.str ":",
                      Pretty.quote (repr_term T tm)])) assumes
 in (Pretty.block o Pretty.breaks) (head@(Pretty.separate "+" parents)@
    (if length (fixes'@assumes') > 0 andalso length parents > 0
     then [Pretty.str "+"] else [])@
    (if length fixes' > 0
      then [Pretty.str "fixes"]@(Pretty.separate "and" fixes') else [])@
    (if length assumes' > 0
      then [Pretty.str "assumes"]@(Pretty.separate "and" assumes') else [])) end

fun repr_locale T (s,fixes,in_loc,_,ps) =
 let val head    = [Pretty.str "locale", repr_name s]
                   @(if length fixes + length in_loc + length ps > 0
                     then [Pretty.str "="] else [])
     val parents  = List.map repr_name ps
     val fixes'   = List.map (fn ((s,tp),_) => Pretty.block (Pretty.breaks
                     [Pretty.str s,Pretty.str "::",
                      Pretty.quote (repr_typ T tp)])) fixes
     val assumes' = List.map (fn (s,tm) => Pretty.block (Pretty.breaks
                     [repr_name s, Pretty.str ":",
                      Pretty.quote (repr_term T tm)])) in_loc
  in (Pretty.block o Pretty.breaks) (head@(Pretty.separate "+" parents)@
    (if length (fixes'@assumes') > 0 andalso length parents > 0
     then [Pretty.str "+"] else [])@
    (if length fixes' > 0
      then [Pretty.str "fixes"]@(Pretty.separate "and" fixes') else [])@
    (if length assumes' > 0
      then [Pretty.str "assumes"]@(Pretty.separate "and" assumes') else [])) end

fun repr_datatype T d =
 let val dts = List.map (fn (s,vs,eqs) => 
                let val vs' = Pretty.enclose "(" ")"
                         (Pretty.separate "," (List.map (repr_typ T) vs))
                    val eqs' = Pretty.separate "|" (List.map
                         (fn (s,vs) => Pretty.block (Pretty.breaks 
                           ([repr_name s]@
                            (List.map (Pretty.quote o repr_typ T) vs)))) eqs)
                in Pretty.block (Pretty.breaks
                    ([vs']@[repr_name s,Pretty.str "="]@eqs')) end) d
 in (Pretty.block o Pretty.breaks) ([Pretty.str "datatype"]@
     Pretty.separate "and" dts) end

fun theory_of_exportable_data T =
 let val datatypes      = datatypes_of T
     val functions      = functions_of T
     val classes_Graph  = String_Graph.make
          (List.map (fn l => ((#1 l,l),#2 l)) (classes_of T))
     val classes_sorted =
          List.rev (String_Graph.topological_order classes_Graph)
     val classes        = List.map
                           (#1 o #2 o (String_Graph.get_entry classes_Graph))
                           classes_sorted
     val locales_Graph  = String_Graph.make
          (List.map (fn l => ((#1 l,l),#5 l)) (locales_of T))
     val locales_sorted =
          List.rev (String_Graph.topological_order locales_Graph)
     val locales        = List.map
                           (#1 o #2 o (String_Graph.get_entry locales_Graph))
                           locales_sorted
 in theory_of_string (unlines (List.map pretty_as_str
    ((List.map (repr_datatype T) datatypes)
    @(List.map (repr_function T) functions)
    @(List.map (repr_class T) classes)
    @(List.map (repr_locale T) locales)))) (Context.parents_of T) end

fun get_basic_theory_data T =
 let val T'  = theory_of_exportable_data T
     val cmp = (fn (s,(s1,_)) =>
                 (lift fast_string_ord unqualify) (s,s1))
     val axs = Ord_List.subtract cmp
                (Ord_List.make fast_string_ord (List.map #1 (axioms_of T')))
                (Ord_List.make (lift fast_string_ord #1) (axioms_of T))
     val thms = Ord_List.subtract cmp
                (Ord_List.make fast_string_ord (List.map #1 ((thms_of T')@axs)))
                (Ord_List.make (lift fast_string_ord #1) (thms_of T))
     val consts = Ord_List.subtract cmp
                (Ord_List.make fast_string_ord (List.map #1 (consts_of T')))
                (Ord_List.make (lift fast_string_ord #1) (consts_of T))
 in (axs, thms, consts) end

fun get_theories T =
 let val Ts = T::(non_image_theories T)
 in List.map (fn T => 
      let val name             = name_of_theory T
          val (axs,thms,consts) = get_basic_theory_data T
          val datatypes        = datatypes_of T
          val functions        = functions_of T
          val classes          = classes_of T
          val locales          = locales_of T
      in (name,axs,thms,consts,datatypes,functions,
          classes,locales) end) Ts end

(* Generate XML Output *)

structure XML_Syntax = Legacy_XML_Syntax

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

(* Enrich the (isabelle-builtin) XML representation of terms with infix information *)
fun mixfix_to_args m = case m of
   SOME(Mixfix.Infixl (s,j)) => [("infixl",s), ("mixfix_i",string_of_int j)]
 | SOME(Mixfix.Infixr (s,j)) => [("infixr",s), ("mixfix_i",string_of_int j)]
 | SOME(Mixfix.Infix (s,j))  => [("infix",s), ("mixifix_i",string_of_int j)]
 | _ => []

fun xml_of_term' T tbl t = case t of
   XML.Elem (("Const",a),t) =>
    let val b = case (Syntax.guess_infix (Sign.syn_of T)
                 (Lexicon.mark_const ((#2 o List.hd) a))) of
                   SOME(mx) => mixfix_to_args (SOME mx)
                 | NONE => mixfix_to_args (Symtab.lookup tbl ((#2 o List.hd) a))
    in XML.Elem (("Const",a@b),map (xml_of_term' T tbl) t) end
 | XML.Elem ((s,a),t) => XML.Elem ((s,a),map (xml_of_term' T tbl) t)
 | _ => t

fun xml_of_term T t = xml_of_term' T Symtab.empty
     (XML_Syntax.xml_of_term t)

fun xml_of_datatype T eqs = XML.Elem (("RecDatatypes",[]),List.map
 (fn (name,type_params,constructors) =>
    XML.Elem (("Datatype",[("name",Long_Name.base_name name)]),
       (List.map XML_Syntax.xml_of_type type_params)
      @(List.map (fn (s,tps) => XML.Elem
         (("Constructor",[("name",Long_Name.base_name s)]),
           List.map XML_Syntax.xml_of_type tps))
         constructors))) eqs)

fun xml_of_function T (name,tp,def_eqs) =
 XML.Elem (("Function",[("name",Long_Name.base_name name)]),
           (XML_Syntax.xml_of_type tp)
  ::(List.map(fn (pats,tm) =>
   XML.Elem (("Equations",[]),List.map (xml_of_term T)
   (pats@[tm]))) def_eqs))

fun xml_of_class T (name,parents,assumps,fixes) =
 XML.Elem (("ClassDef",[("name",Long_Name.base_name name)]),
  (List.map (fn p =>
   XML.Elem (("Parent",[("name",Long_Name.base_name p)]),[])) parents)
 @(List.map (fn (s,t) =>
   XML.Elem (("Assumption",[("name",Long_Name.base_name s)]),
    [xml_of_term T t])) assumps)
 @(List.map (fn (s,t) =>
   XML.Elem (("ClassParam",[("name",Long_Name.base_name s)]),
    [XML_Syntax.xml_of_type t])) fixes))

fun xml_of_locale T (name,fixes,assumps,thms,parents) =
 XML.Elem (("Locale",[("name",Long_Name.base_name name)]),
  (List.map (fn ((s,t),m) =>
   XML.Elem (("LocaleParam",[("name",Long_Name.base_name s)]
     @(mixfix_to_args (SOME m))),
    [XML_Syntax.xml_of_type t])) fixes)
 @(List.map (fn (s,t) =>
   XML.Elem (("Assumption",[("name",Long_Name.base_name s)]),
    [xml_of_term T t])) assumps)
 @(List.map (fn (s,t) =>
   XML.Elem (("Theorem",[("name",Long_Name.base_name s)]),
    [xml_of_term T t])) thms)
 @(List.map (fn p =>
   XML.Elem (("Parent",[("name",Long_Name.base_name p)]),[])) parents))

fun xml_of_theory (name, axs, thms, cs, dts, fns, cls, locales) =
 let val T        = theory_by_name name
     val imports  = List.map
                  (fn T => XML.Elem (("Import",[("name",name_of_theory T)]),[]))
                  (Context.parents_of T)
     val axioms   = List.map (fn (n,t) => XML.Elem
                     (("Axiom",[("name",Long_Name.base_name n)]),
                      [(xml_of_term T o prettify_term) t])) axs
     val theorems = List.map (fn (n,t) => XML.Elem
                     (("Theorem",[("name",Long_Name.base_name n)]),
                      [(xml_of_term T o prettify_term) t])) thms
     val consts   = List.map (fn (n,tp) => XML.Elem
                     (("Const",[("name",Long_Name.base_name n)]),
                      [XML_Syntax.xml_of_type tp])) cs
     val datatypes = List.map (xml_of_datatype T) dts
     val functions = List.map (xml_of_function T) fns
     val classes   = List.map (xml_of_class T) cls
     val locales'  = List.map (xml_of_locale T) locales
 in fixTypeNames name (XML.Elem (("IsaTheory",[("name",name)]),
     imports@axioms@theorems@consts@datatypes
    @functions@classes@locales')) end

fun xml_of_theories theories =
 XML.Elem (("IsaExport",[]),List.map xml_of_theory theories)

end;
