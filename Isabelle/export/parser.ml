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
                            |TxtRaw of string;
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
	|Sublocale of (xstring * Position.T) * (Expression.expression *
                       (Attrib.binding * string) list)
	|Interpretation of Expression.expression *
                           (Attrib.binding * string) list
        |Interpret of Expression.expression *
                      (Attrib.binding * string) list
	|Class of (binding * (string list * Element.context list)) *
                  thy_body list
	|Subclass of string
	|Instantiation of (string list * string list * string) * thy_body list
	|Instance of (string * instance_type) option
	|Overloading of (bstring * string * bool) list * thy_body list
        |Misc of misc_body;
	val hide = curry Hide;
(* Common Functions *)
	(* taken from Pure/Isar/parse.ML *)
	fun RESET_VALUE atom =
          Scan.ahead (Scan.one (K true)) -- atom >>
           (fn (arg, x) => (Token.assign NONE arg; x));
        fun unparse_kind k =
            Parse.group (fn () => Token.str_of_kind k)
             (RESET_VALUE (Scan.one (Token.is_kind k) >> Token.unparse));
        val unparse_verbatim = unparse_kind Token.Verbatim;
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
	val mk_thy_body = List.map (fn (s,p) => Parse.command_name s |-- p);
	val simple_thy_body = Scan.first (mk_thy_body [
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
                      >> Sublocale),
        ("interpretation",                                 (* line 442 *)
         parse_interpretation_arguments true
          >> Interpretation),
	("interpret",                                      (* line 449 *)
         parse_interpretation_arguments true
          >> Interpret),
	("subclass",                                       (* line 471 *)
	 Parse.class >> Subclass),
	("instance",Scan.option (Parse.class --            (* line 481 *)
         (((@{keyword "\<subseteq>"} || @{keyword "<"})
          |-- Parse.!!! Parse.class) >> InstanceSubset
         || Parse.multi_arity >> InstanceArity))
         >> Instance)]);
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
                Parse_Spec.class_expression -- Scan.optional (@{keyword "="}
                 |-- Parse.!!! (Scan.repeat1 Parse_Spec.context_element)) []
                 || Scan.repeat1 Parse_Spec.context_element >> pair []
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
