signature ParserHelper =
sig
	type thy_body
	val cmd_theory : Thy_Header.header parser
	val cmd_header : string parser
	val thy_body : thy_body parser
end;

structure ParserHelper : ParserHelper =
struct
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
	(* isar-ref.pdf page 78 *)
	datatype context_head = ContextNamed of xstring * Position.T
                               |ContextHead  of ((xstring * Position.T) list
                                                * Element.context list);
	datatype instance_type = InstanceArity of string list * string list
                                                 *string
                                |InstanceSubset of string;
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
	|Context of context_head * thy_body list
	|Locale of (binding * (Expression.expression * Element.context list))
                   * thy_body list
	|Sublocale of ((xstring * Position.T) * (Expression.expression *
                        (Attrib.binding * string) list)) * proof
	|Interpretation of (Expression.expression *
                            (Attrib.binding * string) list) * proof
        |Interpret of Expression.expression *
                      (Attrib.binding * string) list
	|Class of (binding * (string list * Element.context list)) *
                  thy_body list
	|Subclass of string * proof
	|Instantiation of (string list * string list * string) * thy_body list
	|Instance of ((string * instance_type) option) * proof
	|Overloading of (bstring * string * bool) list * thy_body list
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
	|Fun of ((Function_Common.function_config * (binding *
                 string option * mixfix) list) *
                (Attrib.binding * string) list)
        |PartialFunction of xstring * ((binding * string option * mixfix) list *
                             (Attrib.binding  * string))
	|Function of ((Function_Common.function_config *
                       (binding * string option * mixfix) list)
                      * (Attrib.binding * string) list) * proof
	|Termination of string option * proof
	|Misc of misc_body;
	val hide = curry Hide;
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
        val cmd_theory = Parse.command_name "theory" |-- Thy_Header.args;
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
	val trfun = Parse.opt_keyword "advanced" -- Parse.ML_source;
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
	fun partition p [] = []
           |partition p (t::l')  = let val (cmd,l'') = take_prefix p l'
                                   in (t::cmd)::(partition p l'') end;
	fun proof_qed i = Parse.group (fn () => "proof_qed") 
                          (fn t =>
                           if i > 0 then Scan.first
                                    [command "qed" -- proof_qed (i-1) >> op::,
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
	val proof = Parse.!!! ((proof_prefix -- Scan.first
                      [command_with_args "proof" -- proof_qed 1 >> op@,
                       command "oops" >> single,
                       command_with_args "by",
                       command ".." >> single,
                       command "." >> single]) >> op@
                     >> ((List.map (List.map Token.unparse)
                         #> List.map (space_implode " ")
                         #> cat_lines) o (partition Token.is_command)));
	val simple_thy_body' = Scan.first (mk_thy_body [
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
                     (Parse.const -- Parse_Spec.locale_mixfix))
                     >> Notation),                         (* line 216 *)
	("no_notation",Parse.opt_target --
                    (opt_mode -- Parse.and_list1
                     (Parse.const -- Parse_Spec.locale_mixfix))
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
	("ML",Parse.ML_source >> ML),                      (* line 280 *)
	("ML_prf",Parse.ML_source >> ML_prf),              (* line 287 *)
	("ML_val",Parse.ML_source >> ML_val),              (* line 293 *)
	("ML_command",Parse.ML_source >> ML_command),      (* line 297 *)
	("setup",Parse.ML_source >> Setup),                (* line 301 *)
	("local_setup",Parse.opt_target --
                       Parse.ML_source >> LocalSetup),     (* line 305 *)
	("attribute_setup",Parse.position Parse.name --    (* line 309 *)
                           Parse.!!! (@{keyword "="} |--
                           Parse.ML_source -- Scan.optional
                           Parse.text "") >> AttributeSetup),
	("method_setup",Parse.position Parse.name --       (* line 315 *)
                           Parse.!!! (@{keyword "="} |--
                           Parse.ML_source -- Scan.optional
                           Parse.text "") >> MethodSetup),
	("declaration",Parse.opt_target --                 (* line 321 *)
                       Parse.opt_keyword "pervasive" --
                       Parse.ML_source >> Declaration),
	("syntax_declaration",Parse.opt_target --          (* line 326 *)
                       Parse.opt_keyword "pervasive" --
                       Parse.ML_source >> SyntaxDeclaration),
	("simproc_setup",Parse.opt_target --               (* line 331 *)
                       Parse.position Parse.name --
                       (@{keyword "("} |-- Parse.enum1 "|"
                        Parse.term --| @{keyword ")"} --|
                        @{keyword "="}) -- Parse.ML_source
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
           (@{keyword "="} |-- Parse.ML_source) >> Oracle),(* line 371 *)
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
	("subclass",                                       (* line 471 *)
	 Parse.class -- proof >> Subclass),
	("instance",Scan.option (Parse.class --            (* line 481 *)
         (((@{keyword "\<subseteq>"} || @{keyword "<"})
          |-- Parse.!!! Parse.class) >> InstanceSubset
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
        ("fun",Function_Common.function_parser
                Function_Fun.fun_config
               >> Fun),
        (* line 285 HOL/Tools/Function/partial_function.ML *)
        ("partial_function",((@{keyword "("} |-- Parse.xname --|
         @{keyword ")"}) -- (Parse.fixes -- (Parse.where_ |--
         Parse_Spec.spec))) >> PartialFunction),
	(* line 284 HOL/Tools/Function/function.ML *)
        ("function",Function_Common.function_parser
                     Function_Common.default_config
                    -- proof
                    >> Function),
        (* line 290 HOL/Tools/Function/function.ML *)
        ("termination",Scan.option Parse.term -- proof
                       >> Termination)]);
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
             Scan.first (List.map (fn s => unparse_cmd s >>
              (Misc o DiagnosticCommand)) diagnostic_commands) ||
             Scan.first (List.map (fn s => unparse_cmd s >>
              (Misc o TopLevelCommand)) diagnostic_commands);
	(* Isabelle/Isar/isar_syn.ML line 415 *)
        val locale_val =
          Parse_Spec.locale_expression false --
          Scan.optional (@{keyword "+"} |-- Parse.!!!
          (Scan.repeat1 Parse_Spec.context_element)) [] ||
          Scan.repeat1 Parse_Spec.context_element >> pair ([], []);
        fun rec_thy_body toks = Scan.first [
	(Parse.command_name "context" |--                  (* line 405 *)
         ((Parse.position Parse.xname >> ContextNamed) ||
          (Scan.optional Parse_Spec.includes [] --
           Scan.repeat Parse_Spec.context_element
           >> ContextHead))
         --| Parse.begin
         -- Scan.repeat (simple_thy_body || rec_thy_body)
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
end;

signature Parser =
sig
        val scan      : string -> Token.T list;
	val dbg       : Token.T list -> (Token.kind * string) list
	datatype thy = Thy of {header:string option,
                               args:Thy_Header.header,
                               body:ParserHelper.thy_body list};
	val thy : Token.T list -> thy
	val parse_typ : theory -> (string * Position.T) option -> string -> typ
end;

structure Parser : Parser = 
struct
	open ParserHelper
        datatype thy = Thy of {header:string option,
                               args:Thy_Header.header,
                               body:thy_body list};
        (* scan isabelle source transforming it into a sequence of commands *)
        fun scan s =   File.read (Path.explode s)
                    |> Source.of_string |> Symbol.source
                    |> Token.source {do_recover = SOME false}
                        Keyword.get_lexicons Position.start
                    |> Token.source_proper |> Source.exhaust;
	val dbg = List.map (fn t => (Token.kind_of t,Token.content_of t));
	val thy = Scan.catch (Scan.option cmd_header -- cmd_theory
                  -- Scan.repeat thy_body
                  --| Parse.command_name "end"
                  #> (fn (((h,a),b),_) => Thy {header=h,args=a,body=b}));
	fun parse_typ T loc =
         let val ctxt = Named_Target.context_cmd (the_default 
                         ("-", Position.none) loc) T
         in Syntax.parse_typ ctxt end;
end;
