signature ParserHelper =
sig
	type ('a,'b) p;
	datatype ('a,'b) r = Result of 'b
                           | More of 'a -> ('a,'b) r
                           | End of 'b
                           | Fail of string;
	val result : 'a list -> ('a -> ('a,'b) r) -> 'a list * ('a,'b) r;
	val p : ('a -> ('a, 'b) r) -> ('a, 'c) p -> ('a, 'c * 'b) p;
	val p2r : (('a, string) p -> ('b, 'c) p) -> 'a list -> ('d, 'c) r;
	val >> : ('a, 'b) p * ('b -> 'c) -> ('a, 'c) p;
	val >>> : ('a -> ('b, 'c) p) * ('c -> 'd) -> 'a -> ('b, 'd) p;
	val >>= : ('a, 'b) p * ('b -> 'c) -> 'c option;
	val getError : ('a, 'b) p -> string;
	val return : 'a -> ('b, 'c) p -> ('b, 'c * 'a) p;
	val initialState : 'a list -> ('a,string) p;
	val pack : ('a, ('b * 'c) * 'd) p -> ('a, 'b * ('c * 'd)) p;
	val expect_end : ('a, 'b) p -> ('c, 'b) p;
	val e : ('a -> ('a, 'b) r) -> ('a, 'c) p -> ('a, 'c) p;
	val succeed : ('a -> ('a, 'b) r) -> ('a, 'c) p -> ('a, 'c) p;
	val many : (('a, 'b) p -> ('a, 'b * 'c) p) ->
                   ('a, 'b) p -> ('a, 'b * 'c list) p;
	val sepBy : (('a, 'b * 'c) p -> ('a, 'd * 'c) p) ->
                    (('a, 'd) p -> ('a, 'b * 'c) p) -> 
                    ('a, 'd) p -> ('a, 'd * 'c list) p;
	val optional : (('a, 'b) p -> ('a, 'b * 'c) p) ->
                       ('a, 'b) p -> ('a, 'b * 'c option) p;
	val oneOf : ('a -> ('b, 'c) p) list -> 'a -> ('b, 'c) p;
end;

infix 1 >> >>> >>=;

structure ParserHelper : ParserHelper =
struct
	(* Parser state consisting either of
            * a valid state containing a list of tokens and a parser result
            * or an error message *)
	datatype ('a,'b) p = State  of ('a list) * 'b
                           | Failed of string;
	(* Parse result:
	    * Result (parsing finished)
            * More (needs to consume more token using returned function)
            * End (parsing ended before the current token - do not consume it)
            * Fail (parsing failed with error message) *)
        datatype ('a,'b) r = Result of 'b
                           | More of 'a -> ('a,'b) r
                           | End of 'b
                           | Fail of string;
	(* Obtain a parser result sensibly handling More and End *)
        fun result [] _      = ([],Fail "No more data!")
          | result (d::ds) f = case f d of
                                More f => result ds f
                               |End v  => (d::ds,Result v)
                               |r      => (ds,r);
        (* Interpret a parsing result as an action on a parser state.
	   Old and new result value are combined as a tuple. 

           "parsers" can be combined using #> and applied in
           sequence using |>  *)
        fun p _ (Failed s)     = Failed s
          | p f (State (ds,v)) = case result ds f of
                                        (ds',Result v1) => State (ds',(v,v1))
                                       |(_,Fail s)      => Failed s
                                       |_               => Failed "Unexpected!";
	(* Interpret a parser state as a parser result *)
	fun p2r' (State (_,v)) = Result v
           |p2r' (Failed s)    = Fail s;
	fun p2r f v = State (v,"") |> f |> p2r';
	
	(* apply f to presult value *)
	fun  (State (d,v)) >> f = State (d,f v)
            |(Failed s)    >> _ = Failed s;
        (* apply g to the result produced by f *)
	fun  (f >>> g) x = x |> f >> g;
	(* extract result and apply f *)
	fun (State (_,v)) >>= f = SOME (f v)
           |(Failed _)    >>= _ = NONE
	fun getError (Failed s) = s
           |getError _          ="";
	(* add result v1 to the state *)
	fun return v1 (State (d,v)) = State (d,(v,v1))
           |return _ (Failed s)     = Failed s;
	fun initialState d = State (d,"");
	(* reorder result tuple *)
	fun pack (State (d,((v,v1),v2))) = State (d,(v,(v1,v2)))
           |pack (Failed s) = Failed s;
	(* expect the end of the token stream
           (useful to check if all tokens were consumed) *)
	fun expect_end (Failed s)     = Failed s
          | expect_end (State ([],v)) = State ([],v)
          | expect_end (State (_,_)) = Failed "Expected end!";
	(* create a parser discarding the result of f *)
	fun e f s = p f s >> #1;
	(* always succeeds, but only consumes input if the
	   parsing is successful *)
	fun succeed f s = case p f s of
                           Failed _          => s
                          |State (ds,(v,_)) => State (ds,v);
	(* apply parser p as many times as possible *) 
	fun many p s =
             case (p s,s) of
              (State (ds,(v,v1)),_)   =>
               let val (ds',vs) = case many p (State (ds,v)) of
                                   State (ds',(_,vs)) => (ds',vs)
			          |Failed _ => (ds,[])
               in State (ds',(v,v1::vs)) end
             |(Failed _,State (ds,v)) => State (ds,(v,[]))
             |(_,Failed s)            => Failed s;
	(* apply parser p multiple times separated by sep *)
	fun sepBy sep p s = case many (p #> sep) s of
                             State (ds,(v,vs)) =>
                              let val (ds',vs') =
                                   case p (State (ds,v)) of
                                    State (ds',(_,v')) => (ds',(v'::vs))
                                   |Failed _ => (ds,vs)
                              in State (ds',(v,vs')) end
                            |Failed s => Failed s;
	(* if p is a parser then optional p either has the result
           SOME("result of p") or NONE (if p fails)

	   if p and p1 are parsers then `optional (p #> p1)`
           is the optional version of `p |> p1` *)
	fun optional _ (Failed s)     = Failed s
           |optional p (State (ds,v)) = case p (State (ds,v)) of
                             Failed _ => State (ds,(v,NONE))
                            |State (ds',(v',v1)) => State (ds',(v',SOME(v1)));
	(* try each of the parsers ps from left to right
           until one succeeds or fail if all parsers fail *)
	fun oneOf ps s = List.foldl (fn (p,s') => case s' of
                                                   Failed _ => p s
                                                   |_ => s')
                          (Failed "No parser supplied") ps;
end;

signature Parser =
sig
	type cmd = Token.T list;
        val scan      : string -> cmd list;
	type parsed_theory;
	val test : cmd list -> (parsed_theory option * string);
end;

structure Parser : Parser =
struct
	open ParserHelper
	(* partition (l : a' list) into sublist according predicate
           (p : 'a -> bool) which signals the start of a new sublist,
	   i.e. the start of each sublist will satisfy p and all
           other elements of each sublist will not. Only the first
           sublist may start with an element that does not satisfy p.
           
           example:  partition (curry op= "a") "abababab"
                   = ["ab","ab","ab","ab"] *)
        fun partition p l = #2 (List.foldr
                (fn (x,(l1,l2)) =>      if (p x) then ([],(x::l1)::l2)
                                        else (x::l1,l2)) ([],[]) l);
	type cmd = Token.T list;
        (* scan isabelle source transforming it into a sequence of commands *)
	fun scan str = str |> Source.of_string |> Symbol.source
                           |> Token.source {do_recover = SOME false}
                                           Keyword.get_lexicons
                                           Position.start
                           |> Token.source_proper |> Source.exhaust
                           |> partition Token.is_command;
	
	datatype local_data = LocalData of
                              {assumes: {name:string option, term:string} list,
                               fixes:   {names:string list, tp:string} list};
	fun mkLocalData a f = LocalData {
                           assumes = List.map (fn (n,t) => {name=n,term=t}) a,
                           fixes = List.map (fn (ns,t) => {names=ns,tp=t}) f };
        datatype theory_body_elem = DataType of (string list * (string *
                                    (string * string list) list)) list
                                   |Consts of (string * string) list
                                   |Axioms of (string * string) list
                                   |Lemma of {name: string,
					      target: string option,
                                              statement: string,
                                              proof: string}
                                   |Theorem of {name: string,
                                                target: string option,
                                                statement: string,
                                                proof: string}
                                   |Class of {name:string,
                                              parents:string list,
                                              local_data:local_data}
                                   |Locale of {name:string,
                                               parents:string list,
                                               local_data:local_data}
                                   |TypeSynonym of string * string
                                   |Function of {name: string,
                                                 tp: string,
                                                 def_eqs: string list}
                                   |PrimRec of {names: (string*string) list,
                                                def_eqs: string list}
                                   |Definition of string * (string*string)
                                   |Text of string
                                   |Section of string;
	datatype parsed_theory = ParsedTheory of {
                                 name: string,
                                 imports: string list,
                                 body: theory_body_elem list
                                };

	(* Add token position to error message *)
	fun failT s t = Fail (s^" at "^Token.pos_of t);
	fun content s t = if Token.content_of t = s then Result true
                          else failT ("Expected content '"^s^"' but found "^
                                      "content '"^Token.content_of t^"'") t;
        fun ident t      = if Token.ident_with (K true) t
                           then Result (Token.content_of t)
                           else failT "Not a valid identifier!" t;
        fun type_ident t = if Token.kind_of t = Token.TypeIdent
                           then Result (Token.content_of t)
                           else failT "Not a TypeIdent!" t;
        fun str_ t       = if Token.kind_of t = Token.String
                           then Result (Token.content_of t)
                           else failT "Not a String!" t;
        fun keyword s t  = if Token.keyword_with (curry op= s) t
                           then Result (Token.content_of t)
                           else failT "Not a valid keyword!" t;
        val parse_theory_head = e (content "theory") #> p ident >>> #2
                                #> e (keyword "imports") #> many (p ident)
                                #> e (keyword "begin") #> expect_end;
	val parse_theory_end = e (content "end") #> expect_end;
	fun parse_local_data a =
                 let val assumes = fn k => e k #>
                                     sepBy (e (keyword "and"))
                                        (optional (p ident #> e (keyword ":"))
                                        #> p str_ #> pack)
                     val fixes = e (keyword "fixes") #>
                                    sepBy (e (keyword "and"))
                                          (many (p ident) #> e (keyword "::")
                                           #> oneOf [p str_,p ident] #> pack)
                 in optional (assumes a) #> optional fixes
                    #> optional (assumes a) (* a = keyword "assumes" *)
                    >>> (fn (((v,a),f),a1) =>
                         (v,mkLocalData (the_default [] a @
                                         the_default [] a1)
                                        (the_default [] f))) end
        val parse_body_elem =
            let val dt_type = e (content "datatype")
                               #> sepBy (e (keyword "and"))
                                   (oneOf [e (keyword "(") #>
                                           sepBy (e (keyword ","))
                                                 (p type_ident) #>
                                           e (keyword ")"),
                                           many (p type_ident), return []]
                                    #> p ident #> e (keyword "=")
                                    #> sepBy (e (keyword "|"))
                                             (oneOf [p ident,p str_]
                                              #> many (oneOf [p ident,p str_])
                                              #> pack)
                                    #> pack #> pack)
                               #> expect_end >>> DataType o #2
                val consts  = e (content "consts") #> many (
                                  p ident #> e (keyword "::") #> p str_ #> pack)
                               #> expect_end >>> Consts o #2
                val axioms  = e (content "axioms") #> many ((p ident)
                               #> e (keyword ":") #> (p str_) #> pack)
                               #> expect_end >>> Axioms o #2
                val cls     = e (content "class") #> p ident
                               #> succeed (keyword "=")
                               #> sepBy (e (keyword "+"))
                                        (p ident)
                               #> succeed (keyword "+")
                               #> parse_local_data (keyword "assumes")
                               >>> (fn (((_,n),ps),l) =>
                                    Class { name = n,parents = ps,
                                            local_data = l})
                val locale     = e (content "locale") #> p ident
                               #> succeed (keyword "=")
                               #> sepBy (e (keyword "+"))
                                        (p ident)
                               #> succeed (keyword "+")
                               #> parse_local_data (keyword "assumes")
                               >>> (fn (((_,n),ps),l) =>
                                    Locale { name = n,parents = ps,
                                             local_data = l})
                val tp_synonym = e (content "type_synonym")
                                  #> p ident #> e (keyword "=")
                                  #> p str_ #> pack >>> TypeSynonym o #2
                val fun_       = e (content "fun") #> p ident
                                  #> e (keyword "::") #> p str_
                                  #> e (keyword "where")
                                  #> sepBy (e (keyword "|"))
                                           (p str_)
                                  >>> (fn (((_,n),t),def) =>
                                        Function { name = n, tp = t,
                                                   def_eqs = def })
		val primrec    = e (content "primrec")
                                 #> sepBy (e (keyword "and"))
                                     (p ident #> e (keyword "::") #>
                                      p str_ #> pack)
                                 #> e (keyword "where")
                                 #> sepBy (e (keyword "|")) (p str_)
                                 >>> (fn ((_,ns),def) =>
                                       PrimRec { names = ns, def_eqs = def })
                val def        = e (content "definition")
                                 #> p ident #> e (keyword "::") #> p str_
                                 #> e (keyword "where") #> p str_
                                 #> pack #> pack >>> Definition o #2
            in oneOf [dt_type,consts,axioms,cls,
                      tp_synonym,fun_,primrec,locale,def]  end;
        fun parse_thm s = e (content s)
                          #> optional (
                             e (keyword "(") #> e (keyword "in")
                             #> p ident #> e (keyword ")"))
                          #> p ident
                          #> e (keyword ":")
                          #> optional (parse_local_data (keyword "assumes")
                                        #> e (keyword "shows")) 
                          #> (p str_) #> pack #> pack #> pack >>> #2;
        fun proof_qed i l cmd = case cmd of
                               t::_  => let val l' = cmd::l
                                            val i' = case Token.content_of t of
                                                      "qed"   => i-1
                                                     |"oops"  => 0
                                                     |"proof" => i+1
                                                     |_       => i
                                        in if i' = 0 then List.rev l' |> Result
                                           else More (proof_qed i' l') end
                              |_ => Fail "Expected non-empty command!";
        fun cmdList2string cmds = List.map (List.map Token.unparse) cmds
                                  |> List.map (space_implode " ")
                                  |> cat_lines;
	val proof = oneOf [p (fn cmd =>
                            case cmd of
                             t::_  => if Token.content_of t = "proof"
                                      then More (proof_qed 1 [cmd])
                                      else Fail "Unexpected command!"
                            |_ => Fail "Expected non-empty command!")
                           >>> (fn (v,cmds) => (v,cmdList2string cmds)),
                          p (fn cmd =>
                              case cmd of
                               t::_ => if Token.content_of t = "by"
                                       then Result [cmd]
                                       else Fail "Unexpected command!"
                              |_ => Fail "Expected non-empty command!")
                          >>> (fn (v,cmds) => (v,cmdList2string cmds))];
        val test = initialState #> p (parse_theory_head |> p2r) >>> #2
                   #> many (oneOf [p (parse_body_elem |> p2r),
                                   p (parse_thm "lemma" |> p2r) #> proof
                                    #> pack >>>
                                    (fn (v,((t,(n,(l,stmt))),prf)) =>
                                      (v,Lemma {name=n,
						target=t,
                                                statement=stmt,
                                                proof=prf})),
                                   p (parse_thm "theorem" |> p2r) #> proof
                                    #> pack >>>
                                    (fn (v,((t,(n,(l,stmt))),prf)) =>
                                      (v,Theorem {name=n,
                                                target=t,
                                                statement=stmt,
                                                proof=prf})),
                                   p (fn cmd => case cmd of
                                    t::ts => if Token.content_of t = "text"
                                            then ts |> List.map Token.unparse
                                                    |> space_implode " "
                                                    |> Result
                                            else Fail "Unexpected command!"
                                   |_    => Fail "Expected non-empty command!")
                                    >>> (fn (v,v1) => (v,Text v1)),
                                   p (fn cmd => case cmd of
                                    t::ts => if Token.content_of t = "section"
                                            then ts |> List.map Token.unparse
                                                    |> space_implode " "
                                                    |> Result
                                            else Fail "Unexpected command!"
                                   |_    => Fail "Expected non-empty command!")
                                    >>> (fn (v,v1) => (v,Section v1))])
                   #> e (parse_theory_end |> p2r)
                   #> expect_end >>> (fn ((n,i),b) =>
                       ParsedTheory {name = n,
                                     imports = i,
                                     body = b})
                   #> (fn v => (v >>= I,getError v));
end;

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
     val dt_desc = fn info => List.map (fn (_,(s,vs,eqs)) =>
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

fun xml_of_datatype _ eqs = XML.Elem (("RecDatatypes",[]),List.map
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
