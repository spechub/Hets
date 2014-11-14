structure TheoryData = struct
	type opt_target = (xstring * Position.T) option;
	datatype misc_body = Chapter of opt_target * string
                            |Section of opt_target * string
                            |Subsection of opt_target * string
                            |Subsubsection of opt_target * string
                            |Text of opt_target * string
                            |TextRaw of opt_target * string
                            |Sect of string
                            |Subsect of string
                            |Subsubsect of string
                            |Txt of string
                            |TxtRaw of string
			    |DiagnosticCommand of string
                            |TopLevelCommand of string;
	type proof = string;
	type ml_text = string * Position.T;
	type orig = Token.T list;
	(* isar-ref.pdf page 78 *)
	datatype context_head = ContextNamed of xstring * Position.T
                               |ContextHead  of ((xstring * Position.T) list
                                                * Element.context list);
	datatype instance_type = InstanceArity of string list * string list *
                                                  string
                                |InstanceSubset of string * string * string;
	datatype thy_body =
         Classes of (binding * string list) list
        |Classrel of (string * string) list
        |DefaultSort of opt_target * string
        |TypeDecl of ((opt_target * string list) * binding) * mixfix
	|TypeSynonym of ((opt_target * string list) * binding) *
                        (string * mixfix)
        |Nonterminal of binding list
        |Arities of (string * string list * string) list
        |Judgement of (binding * string * mixfix)
	|Consts of (binding * string * mixfix) list
	|Syntax of (string * bool) * (string * string * mixfix) list
        |NoSyntax of (string * bool) * (string * string * mixfix) list
        |Translations of (xstring * string) Syntax.trrule list
        |NoTranslations of (xstring * string) Syntax.trrule list
        |Axioms of (Attrib.binding * string) list
	|Defs of (bool * bool) * ((binding * string) * Args.src list) list
        |Definition of opt_target * ((binding * string option * mixfix) option
                       * (Attrib.binding * string))
        |Abbreviation of opt_target * ((string * bool) *
                          ((binding * string option * mixfix) option * string))
        |TypeNotation of opt_target * ((string * bool) * (string * mixfix) list)
        |NoTypeNotation of opt_target * ((string * bool) *
                                         (string * mixfix) list)
        |Notation of opt_target * ((string * bool) * (string * mixfix) list)
        |NoNotation of opt_target * ((string * bool) * (string * mixfix) list)
        |Axiomatization of (binding * string option * mixfix) list *
                           (Attrib.binding * string list) list
	|Theorems of (opt_target * (Attrib.binding *
                      (Facts.ref * Args.src list) list) list) *
                     (binding * string option * mixfix) list
	|Lemmas of (opt_target * (Attrib.binding *
                      (Facts.ref * Args.src list) list) list) *
                     (binding * string option * mixfix) list
	|Declare of (opt_target * (Facts.ref * Args.src list) list list) *
                    (binding * string option * mixfix) list
	|Hide of string * (bool * xstring list)
	|Use of string
	|ML of ml_text
	|ML_prf of ml_text
        |ML_val of ml_text
        |ML_command of ml_text
        |Setup of ml_text
        |LocalSetup of opt_target * ml_text
	|AttributeSetup of (bstring * Position.T) * (ml_text * string)
        |MethodSetup of (bstring * Position.T) * (ml_text * string)
	|Declaration of (opt_target * bool) * ml_text
	|SyntaxDeclaration of (opt_target * bool) * ml_text
	|SimprocSetup of (((opt_target * (bstring * Position.T)) *
                           string list) * ml_text) * xstring list
	|ParseAstTranslation of bool * (string * Position.T)
        |ParseTranslation of bool * (string * Position.T)
        |PrintTranslation of bool * (string * Position.T)
        |TypedPrintTranslation of bool * (string * Position.T)
        |PrintAstTranslation of bool * (string * Position.T)
	|Oracle of (bstring * Position.T) * ml_text
	|Bundle of ((opt_target * binding) * (Facts.ref * Args.src list) list) *
                    (binding * string option * mixfix) list
	|Include of (xstring * Position.T) list
	|Including of (xstring * Position.T) list
	|PrintBundles
	|Context of context_head * (orig * thy_body) list
	|Locale of (binding * (Expression.expression * Element.context list))
                   * (orig * thy_body) list
	|Sublocale of ((xstring * Position.T) * (Expression.expression *
                        (Attrib.binding * string) list)) * proof
	|Interpretation of (Expression.expression *
                            (Attrib.binding * string) list) * proof
        |Interpret of Expression.expression *
                      (Attrib.binding * string) list
	|Class of (binding * (string list * Element.context list)) *
                  (orig * thy_body) list
	|Subclass of opt_target * string * proof
	|Instantiation of (string list * string list * string) *
                          (orig * thy_body) list
	|Instance of (instance_type option) * proof
	|Overloading of (bstring * string * bool) list * (orig * thy_body) list
	|Theorem of (((opt_target * Attrib.binding) *
                      (xstring * Position.T) list) *
                     (Element.context list * Element.statement)) * proof
	|Lemma of (((opt_target * Attrib.binding) *
                    (xstring * Position.T) list) *
                   (Element.context list * Element.statement)) * proof
	|Corollary of (((opt_target * Attrib.binding) *
                        (xstring * Position.T) list) *
                        (Element.context list * Element.statement)) * proof
	|SchematicTheorem of (((opt_target * Attrib.binding) *
                               (xstring * Position.T) list) *
                              (Element.context list * Element.statement)) *
                             proof
        |SchematicLemma of (((opt_target * Attrib.binding) *
                             (xstring * Position.T) list) *
                            (Element.context list * Element.statement)) * proof
        |SchematicCorollary of (((opt_target * Attrib.binding) *
                                 (xstring * Position.T) list) *
                                (Element.context list * Element.statement)) *
                               proof
        |Primrec of (opt_target * (binding * string option * mixfix) list) *
                    (Attrib.binding * string) list
        |Datatype of Datatype.spec_cmd list
        |RepDatatype of string list
        |Fun of opt_target * ((Function_Common.function_config * (binding *
                 string option * mixfix) list) *
                (Attrib.binding * string) list)
        |PartialFunction of xstring * ((binding * string option * mixfix) list *
                             (Attrib.binding  * string))
        |Function of (opt_target * ((Function_Common.function_config *
                       (binding * string option * mixfix) list)
              	      * (Attrib.binding * string) list)) * proof
        |Termination of string option * proof
        |Typedef of (((((string * string option) list * binding) * mixfix) *
          string) * (binding * binding) option) * proof
        |Fixrec of opt_target * ((binding * string option * mixfix) list *
                   (bool * (Attrib.binding * string)) list)
	|Domain of bool * ((((string * string option) list * binding) * mixfix)             * ((binding * (bool * binding option * string) list) * mixfix) list)
            list
        |Misc of misc_body;
end;

signature ParserHelper =
sig
	val cmd_theory : (Token.T list * Thy_Header.header) parser
	val cmd_header : string parser
	val thy_body : (Token.T list * TheoryData.thy_body) parser
	val init_thy : Path.T -> (Token.T list * Thy_Header.header) ->
                       Toplevel.state * (Toplevel.state ->
                        Token.T list -> Toplevel.state)
end;

structure ParserHelper : ParserHelper =
struct
	open TheoryData
	val hide = curry Hide;
	fun preserve_toks f toks =
             let val (v,toks') = f toks
                 val consumed_toks = List.take(toks,List.length toks-
                                                    List.length toks')
             in ((consumed_toks,v),toks') end;
(* Common Functions *)
	(* taken from Pure/Isar/parse.ML *)
	fun RESET_VALUE atom =
          Scan.ahead (Scan.one (K true)) -- atom >>
           (fn (arg, x) => (Token.assign NONE arg; x));
        fun token p = RESET_VALUE (Scan.one p);
	fun unparse_kind k = Parse.group (fn () => Token.str_of_kind k)
             (token (Token.is_kind k) >> Token.unparse);
        val unparse_verbatim = unparse_kind Token.Verbatim;
	val not_command = Parse.group (fn () => "non-command token")
             (token (not o Token.is_command));
	fun command s = Parse.group (fn () => "command "^s)
             (token (fn t => Token.is_command t andalso
                             Token.content_of t = s));
	fun command_with_args s = command s -- Scan.repeat not_command >> op::;
(* Pure/pure_syn.ML *)
	(* line 12 *)
        val cmd_theory = preserve_toks (Parse.command_name "theory"
                          |-- Thy_Header.args);
(* Pure/Isar/isar_syn.ML *)
	(* line 14 *)
        val cmd_header = Parse.command_name "header" |-- unparse_verbatim;
	(* line 133 *)
	val opt_mode =
          (* line 129 *)
          let val mode_spec = (@{keyword "output"} >> K ("", false)) ||
                              Parse.name -- Scan.optional
                               (@{keyword "output"} >> K false) true;
          in Scan.optional (@{keyword "("} |-- Parse.!!!
              (mode_spec --| @{keyword ")"})) Syntax.mode_default end;
	val trans_line = (* line 157 *)
          let val trans_pat = (* line 147 *)
                   Scan.optional
                    (@{keyword "("} |-- Parse.!!! 
                     (Parse.xname --| @{keyword ")"}))
                    "logic" -- Parse.inner_syntax Parse.string
              fun trans_arrow toks = (* line 152 *)
                  ((@{keyword "\<rightharpoonup>"} || @{keyword "=>"})
                   >> K Syntax.Parse_Rule ||
                  (@{keyword "\<leftharpoondown>"} || @{keyword "<="})
                   >> K Syntax.Print_Rule ||
                  (@{keyword "\<rightleftharpoons>"} || @{keyword "=="})
                   >> K Syntax.Parse_Print_Rule) toks
	  in trans_pat -- Parse.!!! (trans_arrow -- trans_pat)
	    >> (fn (left, (arr, right)) => arr (left, right)) end;
	val ml_source = Parse.ML_source >> (fn t => (#text t, #pos t));
	val trfun = Parse.opt_keyword "advanced" -- ml_source;
	fun first' l = Scan.first (List.map preserve_toks l);
	fun parse_interpretation_arguments mandatory = (* line 428 *)
	  Parse.!!! (Parse_Spec.locale_expression mandatory) --
	    Scan.optional
	      (Parse.where_ |-- Parse.and_list1
               (Parse_Spec.opt_thm_name ":" -- Parse.prop)) [];
	(* line 514 *)
	val parse_theorem = Parse.opt_target --
             Scan.optional (Parse_Spec.opt_thm_name ":" --|
             Scan.ahead (Parse_Spec.includes >> K "" ||
             Parse_Spec.locale_keyword ||
             Parse_Spec.statement_keyword)) Attrib.empty_binding --
             Scan.optional Parse_Spec.includes [] --
             Parse_Spec.general_statement;
	val mk_thy_body = List.map (fn (s,p) => Parse.command_name s |-- p);
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
	fun proof_qed i = Parse.group (fn () => "proof_qed") 
                          (fn t =>
                           if i > 0 then Scan.first
                                    [command_with_args "qed" --
                                      proof_qed (i-1) >> op@,
                                     command "oops" >> single,
                                     command_with_args "proof"
                                      -- proof_qed (i+1) >> op@,
                                     (token Token.is_command --
                                      Scan.repeat not_command >> op::)
                                     -- proof_qed i >> op@] t
                           else ([],t));
	val proof_prefix = Scan.repeat (Scan.first
                            [command_with_args "apply",
                             command_with_args "using",
                             command_with_args "unfolding"]) >> flat;
	val unparse_tokens = (List.map (List.map Token.unparse)
                         #> List.map (space_implode " ")
                         #> cat_lines) o (partition Token.is_command);
	val proof = Parse.!!! ((proof_prefix -- Scan.first
                      [command_with_args "proof" -- proof_qed 1 >> op@,
                       command "oops" >> single,
                       command_with_args "by",
                       command ".." >> single,
                       command "." >> single]) >> op@
                     >> unparse_tokens);
	val simple_thy_body' = first' (mk_thy_body [
	("chapter", Parse.opt_target -- unparse_verbatim
                     >> (Misc o Chapter)),                 (* line 19 *)
	("section", Parse.opt_target -- unparse_verbatim
                     >> (Misc o Section)),                 (* line 24 *)
        ("subsection", Parse.opt_target -- unparse_verbatim
                        >> (Misc o Subsection)),           (* line 29 *)
        ("subsubsection", Parse.opt_target -- unparse_verbatim
                           >> (Misc o Subsubsection)),     (* line 34 *)
        ("text", Parse.opt_target -- unparse_verbatim
                  >> (Misc o Text)),                       (* line 39 *)
        ("text_raw", Parse.opt_target -- unparse_verbatim
                      >> (Misc o Text)),                   (* line 44 *)
	("sect", unparse_verbatim >> (Misc o Sect)),       (* line 49 *)
	("subsect", unparse_verbatim >> (Misc o Sect)),    (* line 54 *)
        ("subsubsect", unparse_verbatim
                        >> (Misc o Subsubsect)),           (* line 59 *)
	("txt", unparse_verbatim >> (Misc o Txt)),         (* line 64 *)
        ("txt_raw", unparse_verbatim >> (Misc o TxtRaw)),  (* line 69 *) 
	("classes",Scan.repeat1 (Parse.binding --          (* line 79 *)
                    Scan.optional ((@{keyword "\<subseteq>"}
                     || @{keyword "<"}) |-- Parse.!!!
                    (Parse.list1 Parse.class)) []) >> Classes),
        ("classrel",Parse.and_list1 (Parse.class --        (* line 85 *)
                     ((@{keyword "\<subseteq>"} || @{keyword "<"})
                     |-- Parse.!!! Parse.class)) >> Classrel),
        ("default_sort",Parse.opt_target -- Parse.sort
                         >> DefaultSort),                  (* line 92 *)
        ("type_decl",Parse.opt_target -- Parse.type_args   (* line 99 *)
                     -- Parse.binding -- Parse.opt_mixfix
                     >> TypeDecl),
	("type_synonym",                                   (* line 104 *)
          let val p = Parse.opt_target -- Parse.type_args -- 
                      Parse.binding -- (Parse.$$$ "=" |-- Parse.!!!
                        (Parse.typ -- Parse.opt_mixfix'))
          in p >> TypeSynonym end),
	("nonterminal",Parse.and_list1 Parse.binding
                        >> Nonterminal),                   (* line 110 *)
	("arities",Scan.repeat1 Parse.arity >> Arities),   (* line 115 *)
	("judgement",Parse.const_binding >> Judgement),    (* line 122 *)
        ("consts",Scan.repeat1 Parse.const_binding
                   >> Consts),                             (* line 126 *)
	("syntax",opt_mode -- Scan.repeat1 Parse.const_decl
                   >> Syntax),                             (* line 137 *)
	("no_syntax",opt_mode -- Scan.repeat1 
                      Parse.const_decl  >> Syntax),        (* line 141 *)
	("translations",Scan.repeat1 trans_line
                         >> Translations),                 (* line 162 *)
	("no_translations",Scan.repeat1 trans_line
                         >> NoTranslations),               (* line 166 *)
	("axioms",Scan.repeat1 Parse_Spec.spec >> Axioms), (* line 173 *)
	("defs",                                           (* line 186 *)
          let val opt_unchecked_overloaded =
               Scan.optional (@{keyword "("} |-- Parse.!!!
                (((@{keyword "unchecked"} >> K true) --
                 Scan.optional (@{keyword "overloaded"} >> K true) false ||
                 @{keyword "overloaded"} >> K (false, true)) --|
                 @{keyword ")"})) (false, false);
          in opt_unchecked_overloaded --
              Scan.repeat1 (Parse_Spec.thm_name ":" -- Parse.prop
                             >> (fn ((x, y), z) => ((x, z), y)))
            >> Defs end),
	("definition",Parse.opt_target -- Parse_Spec.constdef
                       >> Definition),                     (* line 195 *)
	("abbreviation",Parse.opt_target --                (* line 199 *)
                         (opt_mode -- (Scan.option
                          Parse_Spec.constdecl --
                          Parse.prop)) >> Abbreviation),
	("type_notation",Parse.opt_target --               (* line 204 *)
                          (opt_mode -- Parse.and_list1
                           (Parse.type_const -- Parse.mixfix))
                         >> TypeNotation),
	("no_type_notation",Parse.opt_target --            (* line 210 *)
                            (opt_mode -- Parse.and_list1
                             (Parse.type_const -- Parse.mixfix))
                            >> NoTypeNotation),
	("notation",Parse.opt_target --
                    (opt_mode -- Parse.and_list1
                     (Parse.const -- Parse.mixfix))
                     >> Notation),                         (* line 216 *)
	("no_notation",Parse.opt_target --
                    (opt_mode -- Parse.and_list1
                     (Parse.const -- Parse.mixfix))
                     >> NoNotation),                       (* line 216 *)
	("axiomatization",Scan.optional Parse.fixes [] --  (* line 231 *)
                          Scan.optional (Parse.where_ |--
                           Parse.!!! (Parse.and_list1
                            Parse_Spec.specs)) []
                          >> Axiomatization),
	("theorems",Parse.opt_target --                    (* line 244 *)
                    Parse_Spec.name_facts --
                    Parse.for_fixes >> Theorems),
        ("lemmas",Parse.opt_target --                      (* line 248 *)
                  Parse_Spec.name_facts --
                  Parse.for_fixes >> Lemmas),
	("declare",Parse.opt_target --                     (* line 251 *)
                   Parse.and_list1 Parse_Spec.xthms1 --
                   Parse.for_fixes >> Declare),
	("hide_class",(Parse.opt_keyword "open" >> not) -- (* line 264 *)
                      Scan.repeat1 Parse.xname
                      >> hide "class"),
	("hide_type",(Parse.opt_keyword "open" >> not) --  (* line 265 *)
                      Scan.repeat1 Parse.xname 
                      >> hide "type"),
	("hide_const",(Parse.opt_keyword "open" >> not) -- (* line 266 *)
                      Scan.repeat1 Parse.xname 
                      >> hide "const"),
	("hide_fact",(Parse.opt_keyword "open" >> not) --  (* line 267 *)
                      Scan.repeat1 Parse.xname 
                      >> hide "fact"),
	("use",Parse.path >> Use),                         (* line 273 *)
	("ML",ml_source >> ML),                           (* line 280 *)
	("ML_prf",ml_source >> ML_prf),              (* line 287 *)
	("ML_val",ml_source >> ML_val),              (* line 293 *)
	("ML_command",ml_source >> ML_command),      (* line 297 *)
	("setup",ml_source >> Setup),                (* line 301 *)
	("local_setup",Parse.opt_target --
                       ml_source >> LocalSetup),     (* line 305 *)
	("attribute_setup",Parse.position Parse.name --    (* line 309 *)
                           Parse.!!! (@{keyword "="} |--
                           ml_source -- Scan.optional
                           Parse.text "") >> AttributeSetup),
	("method_setup",Parse.position Parse.name --       (* line 315 *)
                           Parse.!!! (@{keyword "="} |--
                           ml_source -- Scan.optional
                           Parse.text "") >> MethodSetup),
	("declaration",Parse.opt_target --                 (* line 321 *)
                       Parse.opt_keyword "pervasive" --
                       ml_source >> Declaration),
	("syntax_declaration",Parse.opt_target --          (* line 326 *)
                       Parse.opt_keyword "pervasive" --
                       ml_source >> SyntaxDeclaration),
	("simproc_setup",Parse.opt_target --               (* line 331 *)
                       Parse.position Parse.name --
                       (@{keyword "("} |-- Parse.enum1 "|"
                        Parse.term --| @{keyword ")"} --|
                        @{keyword "="}) -- ml_source
                       -- Scan.optional (@{keyword "identifier"} 
                       |-- Scan.repeat1 Parse.xname) []
                       >> SimprocSetup),
	("parse_ast_translation",trfun >>
          ParseAstTranslation),                            (* line 343 *)
        ("parse_translation",trfun >> ParseTranslation),   (* line 348 *)
        ("print_translation",trfun >> PrintTranslation),   (* line 353 *)
        ("typed_print_translation", trfun >>
          TypedPrintTranslation),                          (* line 358 *)
	("print_ast_translation", trfun >>
          PrintAstTranslation),                            (* line 364 *)
	("oracle", Parse.position Parse.name --
           (@{keyword "="} |-- ml_source) >> Oracle),(* line 371 *)
        ("bundle", Parse.opt_target -- (Parse.binding      (* line 379 *)
          --| @{keyword "="}) -- Parse_Spec.xthms1 --
          Parse.for_fixes >> Bundle),
	("include", Scan.repeat1 (Parse.position
                     Parse.xname) >> Include),             (* line 384 *)
	("including", Scan.repeat1 (Parse.position
                       Parse.xname) >> Including),         (* line 390 *)
	("print_bundles", Scan.succeed PrintBundles),      (* line 396 *)
        ("sublocale", Parse.position Parse.xname --|       (* line 434 *)
                      (@{keyword "\<subseteq>"} ||
                       @{keyword "<"}) --
                       parse_interpretation_arguments false
		      -- proof
                      >> Sublocale),
        ("interpretation",                                 (* line 442 *)
         parse_interpretation_arguments true
         -- proof >> Interpretation),
	("interpret",                                      (* line 449 *)
         parse_interpretation_arguments true
          >> Interpret),
	("subclass", Parse.opt_target --                   (* line 471 *)
	 Parse.class -- proof >> Parse.triple1 >> Subclass),
	("instance",Scan.option (                          (* line 481 *)
         ((Parse.class -- (@{keyword "\<subseteq>"}
                        || @{keyword "<"})
          -- Parse.!!! Parse.class) >> Parse.triple1 >> InstanceSubset
         || Parse.multi_arity >> InstanceArity))
         -- proof >> Instance),
        ("theorem", parse_theorem -- proof >> Theorem),    (* line 525 *)
        ("lemma", parse_theorem -- proof >> Lemma),        (* line 526 *)
        ("corollary", parse_theorem -- proof >> Corollary),(* line 527 *)
	("schematic_theorem", parse_theorem -- proof       (* line 528 *)
                               >> SchematicTheorem),
	("schematic_lemma", parse_theorem -- proof         (* line 529 *)
                             >> SchematicLemma),
        ("schematic_corollary", parse_theorem -- proof     (* line 530 *)
                             >> SchematicCorollary),
	(* line 313 HOL/Tools/Datatype/primrec.ML *)
        ("primrec", Parse.opt_target -- Parse.fixes --
                    Parse_Spec.where_alt_specs >> Primrec),
	(* line 795 HOL/Tools/Datatype/datatype.ML *)
	("datatype",Parse.and_list1 Datatype.spec_cmd
                    >> Datatype),
        (* line 646 HOL/Tools/Datatype/rep_datatype.ML *)
        ("rep_datatype",Scan.repeat1 Parse.term
                        >> RepDatatype),
        (* line 173 HOL/Tools/Function/fun.ML *)
        ("fun",Parse.opt_target -- Function_Common.function_parser
                Function_Fun.fun_config
               >> Fun),
        (* line 285 HOL/Tools/Function/partial_function.ML *)
        ("partial_function",((@{keyword "("} |-- Parse.xname --|
         @{keyword ")"}) -- (Parse.fixes -- (Parse.where_ |--
         Parse_Spec.spec))) >> PartialFunction),
	(* line 284 HOL/Tools/Function/function.ML *)
        ("function",Parse.opt_target -- Function_Common.function_parser
                     Function_Common.default_config
                    -- proof
                    >> Function),
        (* line 290 HOL/Tools/Function/function.ML *)
        ("termination",Scan.option Parse.term -- proof
                       >> Termination),
        (* line 275 HOL/Tools/typedef.ML *)
        ("typedef",Parse.type_args_constrained --
          Parse.binding -- Parse.opt_mixfix --
        (@{keyword "="} |-- Parse.term) --
         Scan.option (@{keyword "morphisms"} |--
         Parse.!!! (Parse.binding -- Parse.binding)) --
         proof >> Typedef),
        (* line 404 HOL/HOLCF/Tools/fixrec.ML *)
        ("fixrec",
          let val opt_thm_name' : (bool * Attrib.binding) parser =
                   @{keyword "("} -- @{keyword "unchecked"} --
                   @{keyword ")"} >> K (true, Attrib.empty_binding)
                || Parse_Spec.opt_thm_name ":" >> pair false
              val spec' : (bool * (Attrib.binding * string)) parser =
                   opt_thm_name' -- Parse.prop >>
                   (fn ((a, b), c) => (a, (b, c)))
              val alt_specs' : (bool * (Attrib.binding * string)) list parser =
                  let val unexpected = Scan.ahead
                       (Parse.name || @{keyword "["} || @{keyword "("})
                  in Parse.enum1 "|" (spec' --| Scan.option
                      (unexpected -- Parse.!!! @{keyword "|"})) end
          in Parse.opt_target -- (Parse.fixes -- (Parse.where_
             |-- Parse.!!! alt_specs')) >> Fixrec end),
	(* line 265 HOL/HOLCF/Tools/Domain/domain.ML *)
        ("domain",
          let val dest_decl : (bool * binding option * string) parser =
                 @{keyword "("} |-- Scan.optional
                (@{keyword "lazy"} >> K true) false --
                (Parse.binding >> SOME) -- (@{keyword "::"}
                 |-- Parse.typ)  --| @{keyword ")"} >> Parse.triple1
                || @{keyword "("} |-- @{keyword "lazy"}
                |-- Parse.typ --| @{keyword ")"}
                 >> (fn t => (true, NONE, t))
                || Parse.typ >> (fn t => (false, NONE, t))

	      val cons_decl = Parse.binding --
                   Scan.repeat dest_decl -- Parse.opt_mixfix

              val domain_decl = (Parse.type_args_constrained --
                   Parse.binding -- Parse.opt_mixfix) --
                   (@{keyword "="} |-- Parse.enum1 "|" cons_decl)

              val domains_decl =
                   Scan.optional (@{keyword "("} |--
                   (@{keyword "unsafe"} >> K true) --|
                    @{keyword ")"}) false --Parse.and_list1 domain_decl
          in domains_decl >> Domain end)]);
	fun unparse_cmd s = Parse.group (fn () => s)
         (fn toks =>
           case toks of
            t::toks' =>
             if Token.is_command t andalso Token.content_of t = s then
              let val (cmd,toks'') = take_suffix Token.is_command toks'
              in (t::cmd |> List.map Token.unparse
                         |> space_implode " ",toks'') end
             else Scan.fail ()
            |[] => Scan.fail ());
	val diagnostic_commands = ["pretty_setmargin","help","print_commands",
         "print_configs","print_context","print_theory","print_syntax",
         "print_abbrevs","print_theorems","print_locales","print_classes",
         "print_locale","print_interps","print_dependencies",
         "print_attributes","print_simpset","print_rules","print_trans_rules",
         "print_methods","print_antiquotations","thy_deps","locale_deps",
         "class_deps","thm_deps","print_binds","print_facts","print_cases",
         "print_statement","thm","prf","full_prf","prop","term","typ",
         "print_codesetup","unused_thms"];
	val toplevel_commands = ["cd","pwd","use_thy","remove_thy",
         "kill_thy","display_drafts","print_drafts","pr","disable_pr",
         "enable_pr","commit","quit","exit","welcome","init_toplevel",
         "linear_undo","undo","undos_proof","cannot_undo","kill",
         "realizers","realizability","extract_type","extract"];
	val simple_thy_body = simple_thy_body' ||
             first' (List.map (fn s => unparse_cmd s >>
              (Misc o DiagnosticCommand)) diagnostic_commands) ||
             first' (List.map (fn s => unparse_cmd s >>
              (Misc o TopLevelCommand)) diagnostic_commands);
	(* Isabelle/Isar/isar_syn.ML line 415 *)
        val locale_val =
          Parse_Spec.locale_expression false --
          Scan.optional (@{keyword "+"} |-- Parse.!!!
          (Scan.repeat1 Parse_Spec.context_element)) [] ||
          Scan.repeat1 Parse_Spec.context_element >> pair ([], []);
        fun rec_thy_body toks = first' [
	(Parse.command_name "context" |--                  (* line 405 *)
         ((Parse.position Parse.xname >> ContextNamed) ||
          (Scan.optional Parse_Spec.includes [] --
           Scan.repeat Parse_Spec.context_element
           >> ContextHead))
         --| Parse.begin
         -- Scan.repeat (simple_thy_body || rec_thy_body)
         --| Parse.command_name "end"
         >> Context),
         (Parse.command_name "locale" |--                  (* line 421 *)
          Parse.binding --
          Scan.optional (@{keyword "="} |-- 
          Parse.!!! locale_val) (([], []), []) --
          ((Parse.begin |-- Scan.repeat
            (simple_thy_body || rec_thy_body)
            --| Parse.command_name "end") ||
           Scan.succeed []) >> Locale),
          (* line 464 *)
          (let val class_val = (* Pure/Isar/isar_syn.ML line 458 *)
                Parse_Spec.class_expression -- Scan.optional (@{keyword "+"}
                |-- Parse.!!! (Scan.repeat1 Parse_Spec.context_element)) [] ||
                Scan.repeat1 Parse_Spec.context_element >> pair []
              val p = Parse.binding -- Scan.optional (@{keyword "="}
                       |-- class_val) ([], [])
          in Parse.command_name "class" |-- p --
             ((Parse.begin |-- Scan.repeat
               (simple_thy_body || rec_thy_body)
              --| Parse.command_name "end") ||
              Scan.succeed []) >> Class end),
          ((Parse.command_name "instantiation" |--         (* line 475 *)
           Parse.multi_arity -- (Parse.begin |--
           Scan.repeat (simple_thy_body ||
                        rec_thy_body)
           --| Parse.command_name "end")) >> Instantiation),
          (let val p = Scan.repeat1 (Parse.name --|        (* line 493 *)
                (@{keyword "\<equiv>"} || @{keyword "=="}) --
                Parse.term -- Scan.optional (@{keyword "("} |--
                (@{keyword "unchecked"} >> K false) --|
                @{keyword ")"}) true >> Parse.triple1)
           in Parse.command_name "overloading" |-- p
              -- (Parse.begin |-- Scan.repeat 
                   (simple_thy_body || rec_thy_body) --|
                  Parse.command_name "end")
              >> Overloading end)
          ] toks;
	val thy_body = simple_thy_body || rec_thy_body;
	(* taken from Pure/Thy/thy_load.ML *)
        fun read init state toks =
             let val end_state =
                           List.foldl (fn (t,s) => Toplevel.command_exception true t s)
                            state (Outer_Syntax.read_spans
                             (#2 (Outer_Syntax.get_syntax ())) toks)
             in end_state end;
	fun init_thy dir (toks,header) =
            let val t = read (K
                (let val {name = (name, _), imports, ...} = header
		     val parents = List.map (Thy_Info.get_theory o #1) imports
	         in Resources.begin_theory dir header parents end))
            in (t Toplevel.toplevel toks,t) end;
end;

signature Parser =
sig
        val scan      : Path.T -> Token.T list;
	val dbg       : Token.T list -> (Token.kind * string) list
	datatype thy = Thy of {header:string option,
                               args:(Token.T list * Thy_Header.header),
                               body:(Token.T list * TheoryData.thy_body)
                                    list};
	val thy : Token.T list -> thy
	val read_sort : Toplevel.state -> (string * Position.T) option
                         -> string -> sort
	val read_typ  : Toplevel.state -> (string * Position.T) option
                          -> string -> typ
	val read_term : Proof_Context.mode -> Toplevel.state ->
                         (string * Position.T) option -> string -> term
        val read_prop : Toplevel.state -> (string * Position.T) option ->
                         string -> term
	val read_class : Toplevel.state -> (string * Position.T) option ->
                          string -> class
        val inferred_param : string -> Toplevel.state ->
                             (string * Position.T) option -> typ
	val pretty_tokens : unit -> unit
	datatype symb =
	  Arg of int |
	  TypArg of int |
	  String of bool * string |
	  Break of int |
	  Block of int * symb list;
	type mixfix
	val format_type_mixfix : string -> Mixfix.mixfix ->
                                 int -> mixfix
        val format_const_mixfix : Toplevel.state -> string -> Mixfix.mixfix ->
                                  typ option -> mixfix
end;

structure Parser : Parser = 
struct
	open ParserHelper
        datatype thy = Thy of {header:string option,
                               args:(Token.T list * Thy_Header.header),
                               body:(Token.T list * TheoryData.thy_body) list};
        (* scan isabelle source transforming it into a sequence of commands *)
        fun scan p =   File.read p
                    |> Source.of_string |> Symbol.source
                    |> Token.source {do_recover = SOME false}
                        Keyword.get_lexicons Position.start
                    |> Token.source_proper
                    |> Source.source Token.stopper
                        (Scan.bulk (Parse.$$$ "--" -- Parse.!!! Parse.document_source
                          >> K NONE || Parse.not_eof >> SOME)) NONE
                    |> Source.map_filter I |> Source.exhaust;
	val dbg = List.map (fn t => (Token.kind_of t,Token.content_of t));
	val thy = Scan.catch (Scan.option cmd_header -- cmd_theory
                  -- Scan.repeat thy_body
                  --| Parse.command_name "end"
                  #> (fn (((h,a),b),_) => Thy {header=h,args=a,body=b}));
	fun read_sort state loc =
         let val ctxt = Named_Target.begin (the_default
                         ("-", Position.none) loc) (Toplevel.theory_of state)
         in Syntax.read_sort ctxt end;
        fun do_read read mode state loc =
         let val ctxt' = Named_Target.begin (the_default
                          ("-", Position.none) loc) (Toplevel.theory_of state)
             val ctxt  = Proof_Context.set_mode mode ctxt'
         in read ctxt end;
	val read_typ  = do_read Syntax.read_typ Proof_Context.mode_default;
	val read_term = do_read Syntax.read_term;
        val read_prop = do_read Syntax.read_prop Proof_Context.mode_default;
	val read_class = do_read Proof_Context.read_class
                                 Proof_Context.mode_default;
        fun inferred_param s state target =
             do_read (Proof_Context.inferred_param s)
                      Proof_Context.mode_default state target |> #1;
	fun pretty_tokens () =   (Token.unparse #> PolyML.PrettyString)
                              |> K |> K |> PolyML.addPrettyPrinter;
	(* Taken from Pure/Syntax/printer.ML *)
	datatype symb = (* line 92 *)
	  Arg of int |
	  TypArg of int |
	  String of bool * string |
	  Break of int |
	  Block of int * symb list;
	type mixfix = symb list * int * int
	(* line 107 *)
	fun xprod_to_fmt (Syntax_Ext.XProd (_, _, "", _)) = NONE
	  | xprod_to_fmt (Syntax_Ext.XProd (_, xsymbs, const, pri)) =
	      let
	        fun arg (s, p) =
	          (if s = "type" then TypArg else Arg)
	          (if Lexicon.is_terminal s then 1000 else p);
	
	        fun xsyms_to_syms (Syntax_Ext.Delim s :: xsyms) =
	              apfst (cons (String (not (exists Symbol.is_block_ctrl (Symbol.explode s)), s)))
	                (xsyms_to_syms xsyms)
	          | xsyms_to_syms (Syntax_Ext.Argument s_p :: xsyms) =
	              apfst (cons (arg s_p)) (xsyms_to_syms xsyms)
	          | xsyms_to_syms (Syntax_Ext.Space s :: xsyms) =
	              apfst (cons (String (false, s))) (xsyms_to_syms xsyms)
	          | xsyms_to_syms (Syntax_Ext.Bg i :: xsyms) =
	              let
	                val (bsyms, xsyms') = xsyms_to_syms xsyms;
	                val (syms, xsyms'') = xsyms_to_syms xsyms';
	              in
	                (Block (i, bsyms) :: syms, xsyms'')
	              end
	          | xsyms_to_syms (Syntax_Ext.Brk i :: xsyms) =
	              apfst (cons (Break i)) (xsyms_to_syms xsyms)
	          | xsyms_to_syms (Syntax_Ext.En :: xsyms) = ([], xsyms)
	          | xsyms_to_syms [] = ([], []);
	
	        fun nargs (Arg _ :: syms) = nargs syms + 1
	          | nargs (TypArg _ :: syms) = nargs syms + 1
	          | nargs (String _ :: syms) = nargs syms
	          | nargs (Break _ :: syms) = nargs syms
	          | nargs (Block (_, bsyms) :: syms) = nargs syms + nargs bsyms
	          | nargs [] = 0;
	      in
	        (case xsyms_to_syms xsymbs of
	          (symbs, []) => SOME (const, (symbs, nargs symbs, pri))
	        | _ => raise Fail "Unbalanced pretty-printing blocks")
	      end;
	
	fun format_type_mixfix name mx nargs =
             let val (Syntax_Ext.Syn_Ext {xprods=p,...}) =
                  Mixfix.syn_ext_types [(name,Mixfix.make_type nargs,mx)]
             in case xprod_to_fmt (List.hd p) of
                 SOME (_,(symbs,_,prio)) => (symbs,nargs,prio)
                |_ => raise Fail ("Failed to format mixfix "^
                                  PolyML.makestring mx) end
	fun format_const_mixfix state name mx tp =
		let val (Syntax_Ext.Syn_Ext {xprods=p,...}) =
                     Mixfix.syn_ext_consts
                      (Sign.is_logtype (Toplevel.theory_of state))
                      [(name,case tp of
                              SOME tp' => tp'
                             |NONE     => Simple_Syntax.read_typ "'a",mx)]
                in case xprod_to_fmt (List.last p) of
                    SOME (_,(symbs,nargs,prio)) => (symbs,nargs,prio)
                   |_ => raise Fail ("Failed to format mixfix "^
                                     PolyML.makestring mx) end
end;

structure XML_Helper = struct
	fun variant (vname : string) (mk : 'a -> string)
                    (fs : ('a -> 'b) list) (v : 'a)
             = case get_first (fn f => SOME (f v)
                                handle General.Match => NONE) fs of
                SOME result => result
               |NONE        => raise Fail
                 (vname^" not implemented for "^
                  (mk v |> space_explode " " |> List.hd));
	fun attr (name : string) (f : 'a -> string) (v : 'a) =
             [(name,f v)];
	fun a (name : string) (v : string) = attr name I v;
	fun attr_of_option (vname : string) (name : string) (f : 'a -> string)
             = variant vname (K "") [fn SOME v' => attr name f v',
                                     fn NONE    => []];
	fun xml name attrs body = XML.Elem ((name,attrs),body);
        fun xml' name body attrs = xml name attrs body;
end;

signature Export =
sig
	val xml_of_theory    : (string -> unit) -> string -> XML.tree list
	val get_non_image_parents : theory -> theory list
end;

structure Export : Export =
struct
	fun get_non_image_parents T = List.concat (List.map
	     (fn T' => if length (Thy_Info.loaded_files
                           (Context.theory_name T')) > 0
	               then T'::(get_non_image_parents T') else [])
	     (Context.parents_of T))
	structure XML_Syntax =
	struct
		val xml_of_type = the_single o Term_XML.Encode.typ;
		val xml_of_term = the_single o Term_XML.Encode.term;
	end
	open TheoryData
	open XML_Helper
	datatype thy = datatype Parser.thy;
	
	val xml_of_import  = attr "name" #1 #> xml' "Import" [];
	val xml_of_keyword = variant "xml_of_keyword" PolyML.makestring
             [fn (s,SOME ((s1,[]),[])) => a "name" ("\""^s^"\" :: "^s1),
              fn (s,NONE)              => a "name" s] #> xml' "Keyword" [];
	fun xml_of_use (p,b) = xml "UseFile" (attr "name"
             (Path.print #> b ? (fn s => "("^s^")")) p) [];
	val xml_of_expr = variant "xml_of_expr" PolyML.makestring
             [fn ((name,_),(("",false),Expression.Named [])) =>
               a "name" name] #> xml' "Parent" [];
	local
		val unqualified = Binding.qualified_name #> Binding.name_of;
        	fun extract_context (t : Token.T list)
                                    (body : (Token.T list * 'b) list) =
                     let val btoks = List.map #1 body |> flat
                         val blen = List.length btoks
                         val len  = List.length t
                         fun eq t1 t2 = (Token.kind_of t1 = Token.kind_of t2)
                                        andalso (Token.content_of t1 =
                                                 Token.content_of t2)
                     in if blen = 0 then (t,[])
                        else
                         if not (eq (List.nth (t,len-blen-1)) (List.hd btoks))
                          orelse not (eq (List.nth (t,len-2)) (List.last btoks))
                         then raise (Fail "extract_context failed!")
                         else (List.take (t,len-blen-1),
                               [List.last t]) end;
		val attr_of_target =
                     attr_of_option "attr_of_target" "target" #1;
		fun xml_of_typ state target (SOME typ) = [
                       Parser.read_typ state target typ
                    |> XML_Syntax.xml_of_type]
                   |xml_of_typ _ _ _ = [];
		fun string_of_binding b =
                        let val b' = Binding.print b
                        in String.substring (b',1,String.size b'-2) end;
		val attr_of_binding = attr "name" string_of_binding;
		fun attrs_of_binding state (name,args) =
                     attr_of_binding name@
                     attr "args" (List.map (Args.pretty_src (
                      Toplevel.context_of state) #> Pretty.string_of)
                      #> space_implode ", ") args;
		fun xml_of_symb v = variant "xml_of_symb" PolyML.makestring [
                     fn Parser.Arg i =>
                      xml "Arg" (attr "prio" string_of_int i) [],
                     fn Parser.TypArg i =>
                      xml "Arg" (attr "prio" string_of_int i) [],
                     fn Parser.String (_,s) =>
                      xml "String" (a "val" s) [],
                     fn Parser.Break i =>
                      xml "Break" (attr "prio" string_of_int i) [],
                     fn Parser.Block (i,symbs) =>
                      xml "Block" (attr "prio" string_of_int i)
                                  (List.map xml_of_symb symbs)] v;
                fun format_mixfix state name tp = variant "format_mixfix"
                     PolyML.makestring
                     [fn Mixfix.NoSyn => NONE,
                      fn mx => Parser.format_const_mixfix state name mx tp
                               |> SOME];
		fun format_type_mixfix name num_args = variant
                     "format_type_mixfix" PolyML.makestring
                     [fn Mixfix.NoSyn => NONE,
                      fn mx => Parser.format_type_mixfix name mx num_args
                               |> SOME];
		fun xml_of_mixfix state name tp mx = 
                    case format_mixfix state name tp mx of
                     SOME (symbs,nargs,prio) =>
                       [xml "Mixfix" (attr "nargs" string_of_int nargs@
                                      attr "prio"  string_of_int prio@
                                      attr "pretty" (Mixfix.pretty_mixfix
                                       #> Pretty.str_of) mx)
                         (List.map xml_of_symb symbs)]
                    |NONE => [];
		fun xml_of_type_mixfix name mx num_args =
                    case format_type_mixfix name num_args mx of
                     SOME (symbs,nargs,prio) =>
                      [xml "Mixfix" (attr "nargs" string_of_int nargs@
                                      attr "prio"  string_of_int prio@
                                      attr "pretty" (Mixfix.pretty_mixfix
                                       #> Pretty.str_of) mx)
                         (List.map xml_of_symb symbs)]
                    |NONE => []
		fun xml_of_context state target = variant "xml_of_context"
                     PolyML.makestring
                     [fn Element.Fixes fixes => List.map (fn (b,_,mx) =>
                          xml "Fix" (attr_of_binding b)
                           (let val name = string_of_binding b
				val tp = Parser.inferred_param name state target
                            in [XML_Syntax.xml_of_type tp]@
                               xml_of_mixfix state name (SOME tp) mx end)) fixes
                       |> xml "Fixes" [],
                      fn Element.Assumes ass => List.map (fn (b,tms) =>
                             variant "xml_context (Assumes)"
                              PolyML.makestring [fn [(tm,[])] =>
                               [Parser.read_term Proof_Context.mode_default
                                state target tm |> XML_Syntax.xml_of_term]] tms
                          |> xml "Assumption" (attrs_of_binding state b)) ass
                       |> xml "Assumes" []];
		local
		fun strip_cfun (Const(@{const_name Rep_cfun},_)$f$f1) =
                    strip_cfun f@[f1]
		  | strip_cfun u = [u]
		fun dest_eqs t = HOLogic.dest_eq (HOLogic.dest_Trueprop t)
		fun strip_alls t =
		  (case try Logic.dest_all t of
		    SOME (_, u) => strip_alls u
		  | NONE => t)
		in
		fun split_fixrec_equations state target f eqs =
                    let val (skips, raw_spec) = ListPair.unzip eqs
                        val (fixes, spec) = fst (Specification.read_spec f
                             raw_spec (Toplevel.context_of state))
			val get_tms = (fn (lhs,rhs) => (strip_cfun lhs,rhs)) o
                                       dest_eqs o Logic.strip_imp_concl
			val get_imps = map HOLogic.dest_Trueprop o
                                       Logic.strip_imp_prems
                        val tms = map ((fn x => (get_imps x,get_tms x)) o
                                       strip_alls o snd) spec
			val tms' = ListPair.zip (skips,tms)
			val fn_eqs = List.foldl (fn (eq,t) =>
                             let val (b,(imps,((c::vs),def_tm))) = eq
                                 val (name,tp)     = dest_Free c
                                 val old = Symtab.lookup t name
                             in case old of
                                 SOME (_,def_tms) =>
                                  Symtab.update (name,(tp,def_tms@
                                                 [(b,imps,vs,def_tm)])) t
                                |NONE => Symtab.update (name,(tp,
                                          [(b,imps,vs,def_tm)])) t
                             end) Symtab.empty tms'
			val fns = List.foldl (fn (((b,_),mx),t) =>
                             Symtab.update (Binding.name_of b,mx) t)
                             Symtab.empty fixes
                    in Symtab.fold_rev (fn (k,(tp,equations)) =>
                        let val b = unqualified k
                            val SOME(mx) = Symtab.lookup fns b
                            val equations' = List.map (fn (b,imps,vs,tm) =>
                                 let val imps' = xml "Premises" [] (List.map
                                          (XML_Syntax.xml_of_term) imps)
                                 in xml "FixrecEquation" (if not b then [] else
                                  a "unchecked" "") (imps'::List.map
                                  XML_Syntax.xml_of_term (vs@[tm])) end)
                                 equations
                            val elem = xml "FixrecFun" (a "name" b)
                                 (xml_of_mixfix state b (SOME tp) mx@
                                  [XML_Syntax.xml_of_type tp]@
                                  equations')
                        in fn l => elem::l end) fn_eqs [] end end;
		fun split_equations state target f eqs =
                    let val eqs' = List.map (fn ((b,l),tm) =>
                             let val _ = if Attrib.is_empty_binding (b,l)
                                         then () else raise Fail
                                                ("Not yet implemented "^
                                                 "for split_equations!")
                             in Parser.read_term
                                 Proof_Context.mode_pattern state target tm |>
                                 HOLogic.dest_eq |> (fn (head,body) =>
                                 (strip_comb head,body)) end) eqs
                        val fn_eqs = List.foldl (fn (eq,t) =>
                             let val ((c,vs),def_tm) = eq
                                 val (name,tp)     = dest_Const c
                                 val old = Symtab.lookup t name
                             in case old of
                                 SOME (_,def_tms) =>
                                  Symtab.update (name,(tp,def_tms@
                                                          [(vs,def_tm)])) t
                                |NONE => Symtab.update (name,(tp,
                                          [(vs,def_tm)])) t
                             end) Symtab.empty eqs'
			val fns = List.foldl (fn ((b,_,mx),t) =>
                             Symtab.update (Binding.name_of b,mx) t)
                             Symtab.empty f
                    in Symtab.fold_rev (fn (k,(tp,equations)) =>
                        let val b = unqualified k
                            val SOME(mx) = Symtab.lookup fns b
                            val equations' = List.map (fn (vs,tm) =>
                                 xml "Equation" [] (List.map
                                  XML_Syntax.xml_of_term (vs@[tm]))) equations
			    val elem = xml "Fun" (a "name" b)
                                 (xml_of_mixfix state b (SOME tp) mx@
                                  [XML_Syntax.xml_of_type tp]@
                                  equations')
                        in fn l => elem::l end) fn_eqs []
                    end;
		fun xml_of_statement state target name =
                    variant "xml_of_statement" PolyML.makestring
                     [fn Element.Shows s => List.map (fn (b,tms) =>
                       xml "Shows"
                        (if string_of_binding (#1 b) = "" then
                          attr_of_binding name
                         else attrs_of_binding state b)
                        (List.map (fn (t,ts) => xml "Show" [] (
                          let val t' = Parser.read_term
                                        Proof_Context.mode_default
                                        state target t |> XML_Syntax.xml_of_term
                              val ts' = List.map (Parser.read_term
                                         Proof_Context.mode_schematic
                                         state target #>
                                        XML_Syntax.xml_of_term) ts
                          in t'::ts' end)) tms)) s];
		fun attr_of_function_config
                    (Function_Common.FunctionConfig {sequential,
                     default,domintros,partials}) =
                      (if sequential then a "sequential" "" else [])
                     @(Option.map (a "default") default |> the_default [])
                     @(if domintros  then a "domintros"  "" else [])
                     @(if partials   then a "partials"   "" else []);
		fun xml_of_sort s = xml "Sort" []
                 (List.map (fn n => xml "class" (a "name" n) []) s)
                fun xml_of_arity (s,s') = xml "Arity" []
                     (List.map xml_of_sort (s'::s))
        in fun xml_of_body_elem ((toks,e),((state,trans),l)) =
            let val (elem,state')   = variant "xml_of_body" PolyML.makestring [
                  fn Defs ((unchecked,overloaded),l) =>
                  let val l' = List.map (fn ((name,tm),args) =>
                          let val tm' = Parser.read_prop state NONE tm
                              val (c,def_tm) = Logic.dest_equals tm'
                              val (cname',tp) = dest_Const c
                              val cname = unqualified cname'
                              val args' = List.map (Args.pretty_src
                                 (Toplevel.context_of state) #> Pretty.str_of)
                                 args |> space_implode " "
                          in xml "Def" (a "args" args'@attr_of_binding name@
                                        a "const" cname)
                              [XML_Syntax.xml_of_type tp,
                               XML_Syntax.xml_of_term def_tm] end) l
                      val attrs = (if unchecked then a "unchecked" "" else [])
                                 @(if overloaded then a "overloaded" "" else [])
                  in (xml "Defs" attrs l',trans state toks) end,
                  fn Typedef (((((vars,tp),mx),tm),morphisms),proof) =>
                  let val vars' = List.map (fn (name,sort) => case sort of
                       SOME sort' => TFree (name,
                        Parser.read_sort state NONE sort')
                      |NONE => TFree (name,[])) vars
                      val tm' = Parser.read_term Proof_Context.mode_default
                                 state NONE tm
		      val morphisms' = case morphisms of
                               SOME (m1,m2) => attr "m1" string_of_binding m1@
                                               attr "m2" string_of_binding m2
                              |NONE => []
                      val mx' = xml_of_type_mixfix (string_of_binding tp)
                                 mx (List.length vars)
                  in (xml "Typedef" (attr "type" string_of_binding tp
                                    @morphisms')
                      (mx'@[xml "Proof" [] [XML.Text proof]]@
                       [XML_Syntax.xml_of_term tm']@
                       List.map XML_Syntax.xml_of_type vars'),
                      trans state toks) end,
		  fn Instantiation (arity,body) =>
                  let val ([name],args',sort)  = Class.read_multi_arity
                       (Toplevel.theory_of state) arity
                      val args = List.map #2 args'
                      val (begin_,end_) = extract_context toks body
                      val s1 = trans state begin_
                      val ((s2,_),b_elems) =
                           List.foldl xml_of_body_elem ((s1,trans),[]) body
                      val s3 = trans s2 end_
                  in (xml "Instantiation" (a "type" name)
                       ([xml_of_arity (args,sort)]@
                        [xml "Body" [] (List.rev b_elems)]),s3) end,
		  fn Instance (head,proof) =>
                  let val s1 = trans state toks
                      val (attrs,elems) = case head of
                           SOME (InstanceArity arity) =>
                            let val (names,args',sort)  =
                                 Class.read_multi_arity
                                  (Toplevel.theory_of state) arity
                                val args = List.map #2 args'
				val vars = xml "Vars" [] (List.map (fn s =>
                                     TFree (s,[]) |> XML_Syntax.xml_of_type)
                                    names)
                            in ([],
                                ([vars,xml_of_arity (args,sort)]))
                            end
                          |SOME (InstanceSubset (cls,rel,cls1)) =>
                           (a "class" cls@a "rel" rel@a "class1" cls1,[])
                          |NONE => ([],[])
                  in (xml "Instance" attrs
                       ([xml "Proof" [] [XML.Text proof]]@elems), s1) end,
		  fn Subclass (target,cls,proof) =>
                  let val s1 = trans state toks
                  in (xml "Subclass" (a "class"
                      (Parser.read_class state target cls)@
                      attr_of_target target)
                      [xml "Proof" [] [XML.Text proof]],
                      s1) end,
                  fn Locale ((name,(parents,ctxt)),body) =>
                  let val (begin_,end_) = extract_context toks body
                       val s1 = trans state begin_
                       val ((s2,_),b_elems) =
                            List.foldl xml_of_body_elem ((s1,trans),[]) body
                       val s3 = trans s2 end_
		       val parents' = variant "xml_of_body_elem (Locale)"
                            PolyML.makestring
                            [fn (ps,[]) => List.map xml_of_expr ps] parents
		       val name'  = attr_of_binding name
		       val target = SOME (string_of_binding name,Position.none)
		       val ctxt'  = xml "Ctxt" []
                                     (List.map (xml_of_context s1 target) ctxt)
		   in (xml "Locale" name' (ctxt'::parents'@
                        [xml "Body" [] (List.rev b_elems)]),s3) end,
		 fn Class ((name,(parents,ctxt)),body) =>
                   let val (begin_,end_) = extract_context toks body
                       val s1 = trans state begin_
                       val ((s2,_),b_elems) =
                            List.foldl xml_of_body_elem ((s1,trans),[]) body
                       val s3 = trans s2 end_
		       val target = SOME (string_of_binding name,Position.none)
		       val parents' = List.map (attr "name"
                              (Parser.read_sort s1 target #> the_single)
                           #> xml' "Parent" []) parents
                         handle List.Empty => raise Fail
                          "Unhandled case in xml_of_body_elem (Class)"
                       val name'  = attr_of_binding name
                       val ctxt'  = xml "Ctxt" []
                                    (List.map (xml_of_context s1 target) ctxt)
                   in (xml "Cls" name' (ctxt'::parents'@
                        [xml "Body" [] (List.rev b_elems)]),s3) end,
                 fn TypeSynonym (((target,vars),name),(typ,mx))
                              =>
                   let val s1      = trans state toks
                       val typ'    = Parser.read_typ state target typ
                                     |> XML_Syntax.xml_of_type
		       val name'   = attr_of_binding name
		       val target' = attr_of_target target
		       val mx'     = xml_of_type_mixfix (string_of_binding name)
                                      mx (List.length vars)
		       val vars'   = xml "Vars" [] (List.map
                         (fn s => TFree (s,[]) |> XML_Syntax.xml_of_type)
                          vars)
                   in (xml "TypeSynonym" (name'@target')
                       (mx'@[vars']@[typ']),s1) end,
		 fn Datatype dts =>
                   let val s1 = trans state toks
		       val dts' = List.map
                        (fn ((name,vars,mx),cs) => xml "Datatype"
                          (attr_of_binding name)
                          (xml_of_type_mixfix (string_of_binding name)
                           mx (List.length vars)@
                           List.map (fn (c,tms,mx) =>
                             let val cname = string_of_binding c
                                 val tps = List.map
                                      (Parser.read_typ s1 NONE) tms
			 	 val tp = (tps ---> Type
                                      (string_of_binding name,
                                             List.map (fn (v,s) =>
                                              TFree (v,case s of
                                                SOME(s') => Parser.read_sort
                                                 state NONE s'
                                               |NONE     => [])) vars))
				 val is_c = not (String.isSubstring " " cname)
                                 val attrs = if is_c then attr_of_binding c
                                             else []
                                 val elems' = List.map XML_Syntax.xml_of_type
                                     (if is_c then (tp::tps)
                                      else (Parser.read_typ s1 NONE cname::tps))
			         val elems  = if is_c then (xml_of_mixfix s1
                                      cname (SOME tp) mx@elems') else elems'
                             in xml "Constructor" attrs elems end) cs
                           @(List.map (fn (v,s) =>
                            XML_Syntax.xml_of_type (TFree (v,
                             case s of
                              SOME(s') => [s']
                             |NONE     => []))) vars))) dts
                   in (xml "Datatypes" [] dts', s1) end,
		 fn Consts cs => (xml "Consts" [] (List.map
                   (fn (name,tp,mx) =>
                    let val tp' = Parser.read_typ state NONE tp
                        val name' = string_of_binding name
                        val mx' = xml_of_mixfix state name' (SOME tp') mx
                    in xml "ConstDef" [("name",name')]
                     (mx'@[tp' |> XML_Syntax.xml_of_type]) end) cs),
                    trans state toks),
		 fn Axioms axs => (xml "Axioms" [] (List.map
                   (fn (b,tm) => xml "Axiom"
                    (attrs_of_binding state b)
                    [Parser.read_term Proof_Context.mode_default state NONE tm
                     |> XML_Syntax.xml_of_term]) axs), trans state toks),
		 fn Lemma ((((target,(name,args)), strs),(ctxt,stmt)),proof) =>
                  let val result = case (args,strs) of
                   ([],[]) =>
                    let val s1 = trans state toks
                        val ctxt' = xml "Ctxt" []
                                   (List.map (xml_of_context state target) ctxt)
                    in (xml "Lemma" (attr_of_target target)
                         (ctxt'::[xml "Proof" [] [XML.Text proof]]
                         @xml_of_statement state target name stmt),s1) end
                  |_ => raise Fail ("Case not implemented: "^PolyML.makestring
                                    (args,strs))
                  in result end,
		 fn Definition (target,(name,(binding,tm))) =>
                   let val s1 = trans state toks
                       val _ = case binding of
                                (b,[]) => if string_of_binding b <> "" then
                                 raise Fail "Case not implemented" else ()
                               |_ => raise Fail "Case not implemented"
                       val ((_,[(_,tm')]),_) =
                            Specification.read_free_spec (the_list name)
                             [(binding,tm)] (Toplevel.context_of state)
                       val tm'' = HOLogic.dest_Trueprop tm'
                                  handle ex => tm'
                       val (((name',tp),vs),def_tm) = tm'' |>
                            (fn t => (HOLogic.dest_eq t
                             handle ex => Logic.dest_equals t))
                            |> (fn (head,body) =>
                             case strip_comb head of
                              (f,vs) => ((dest_Free f,vs),body))
                       val mx' = case name of
                            SOME (_,_,mx) => xml_of_mixfix state name' (SOME tp)
                                              mx
                           |NONE => []
                   in (xml "Definition" (a "name" name'@
                                         attr_of_target target)
                        (mx'@[XML_Syntax.xml_of_type tp]@
                         List.map XML_Syntax.xml_of_term (vs@[def_tm])),s1) end,
		 fn Fun (target,((cfg,f),a)) =>
                   let val s1 = trans state toks
		       val elems = split_equations s1 target f a
                   in (xml "Funs" (attr_of_target target
                                  @attr_of_function_config cfg) elems,s1) end,
		 fn Primrec ((target,f),a) =>
                   let val s1 = trans state toks
                       val elems = split_equations s1 target f a
                   in (xml "Primrec" (attr_of_target target) elems,s1) end,
                 fn Fixrec (target,(f,a)) =>
                   let val s1 = trans state toks
                       val elems = split_fixrec_equations s1 target f a
                   in (xml "Fixrec" (attr_of_target target) elems,s1) end,
                 fn Domain (unsafe,dts) =>
                   let val s1   = trans state toks
                       val dts' = List.map (fn (((vs,name),mx), cs) =>
                           let val vars = List.map (fn (a,s) =>
                                    TFree (a, case s of
                                     SOME s' => Parser.read_sort state NONE s'
                                    |NONE    => [])) vs
                               val mx' = xml_of_type_mixfix (string_of_binding
                                          name) mx (List.length vs)
                               val cs' = List.map (fn ((c,args),mx1) =>
                                    let val t = string_of_binding c |>
                                         Parser.read_term
                                          Proof_Context.mode_default s1 NONE
                                         |> Term.type_of in
                                    xml "DomainConstructor" (attr_of_binding c)
                                     ([XML_Syntax.xml_of_type t]@
                                      (List.map (fn (l,sel,tp) =>
                                      xml "DomainConstructorArg"
                                          ((if l then a "lazy" "" else [])
                                           @(case sel of
                                              SOME sel' => attr_of_binding sel'
                                             |NONE => []))
                                          [XML_Syntax.xml_of_type
                                            (Parser.read_typ s1 NONE tp)]))
                                      args) end) cs
                           in xml "Domain" (attr_of_binding name)
                               (mx'@List.map XML_Syntax.xml_of_type vars@cs')
                           end) dts
                   in (xml "Domains" [] dts',s1) end] e
             in ((state',trans),elem::l) end end;
	fun xml_of_body state body =
              List.foldl xml_of_body_elem (state,[]) body;
	fun xml_of_theory v file' =
	    let val _            = v ("Reading "^file'^"\n")
                val file         = file' |> Path.explode |> Path.expand |>
                 File.full_path Path.current |> File.check_file
		val dir          = Path.dir file
                val tname        = Path.explode file' |> Path.base |>
                                   Path.implode
                val (Thy {header,args=(th,h),body}) =
                 file |> Parser.scan |> Parser.thy
		val _            = v ("Loading parents of theory "^tname^"\n")
                val thys         = map (fn (i,_) => (Thy_Info.get_theory i; [])
                                    handle ex =>
                                     let val full = Path.explode i |>
                                          Path.ext "thy" |> File.full_path dir
                                          |> File.check_file |> Path.implode
                                     in xml_of_theory v full end) (#imports h)
                                   |> flat
                val imports      = List.map xml_of_import (#imports h)
		val keywords     = List.map xml_of_keyword (#keywords h)
		val uses         = [] (*List.map xml_of_use (#uses h)*)
                val name         = attr "name" #1 (#name h)
		val header'      = attr_of_option "header" "header" I header 
		val (s,t)        = ParserHelper.init_thy dir (th,h)
                val _            = v ("Exporting theory "^tname^"\n")
		val (s',body'')  = xml_of_body (s,t) body
                val _            = ()(*Toplevel.command_exception true (Toplevel.exit
                                    Toplevel.empty) (#1 s') |>
                                   Toplevel.end_theory Position.none |>
                                   Thy_Info.register_thy*)
                val body'        = [body'' |> List.rev |> xml "Body" []]
            in thys@[xml "Thy" (name@header') (imports@keywords@body')] end;
end;
