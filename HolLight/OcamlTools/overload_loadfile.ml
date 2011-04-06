(* !!!!!!! You must set this to point at the source directory in
   !!!!!!! which OCaml was built. (And don't do "make clean" beforehand.)
 
  the provided value is an example that works with a standard ocaml installation (aptitude install ocaml) on ubuntu

 *)

let ocaml_source_dir = "/usr/lib/ocaml/compiler-libs/";;

let rec do_list f l =
  match l with
    [] -> ()
  | (h::t) -> (f h; do_list f t);;

do_list (fun s -> Topdirs.dir_directory(Filename.concat ocaml_source_dir s))
        ["parsing"; "typing"; "toplevel"; "utils"];;

(* This must be loaded first! It is stateful, and affects Predef *)
#load "ident.cmo";;

#load "misc.cmo";;
#load "path.cmo";;
#load "types.cmo";;
#load "btype.cmo";;
#load "tbl.cmo";;
#load "subst.cmo";;
#load "predef.cmo";;
#load "datarepr.cmo";;
#load "config.cmo";;
#load "consistbl.cmo";;
#load "clflags.cmo";;
#load "env.cmo";;
#load "ctype.cmo";;
#load "printast.cmo";;
#load "oprint.cmo";;
#load "primitive.cmo";;
#load "printtyp.cmo";;

let hol_dir = ref
  (try Sys.getenv "HOLLIGHT_DIR" with Not_found -> Sys.getcwd());;

if let v = String.sub Sys.ocaml_version 0 4 in
   v = "3.10" or v = "3.11"
then (Topdirs.dir_directory "+camlp5";
      Topdirs.dir_load Format.std_formatter "camlp5o.cma")
else (Topdirs.dir_load Format.std_formatter "camlp4o.cma");;

Topdirs.dir_load Format.std_formatter (Filename.concat (!hol_dir) "pa_j.cmo");;

#use "/home/sternk/hol_light/sys.ml";;
#use "/home/sternk/hol_light/lib.ml";;
#use "/home/sternk/hol_light/fusion.ml";;

module OldToploop = Toploop;;
module OldTopdirs = Topdirs;;

let use_file s =
  if Toploop.use_file Format.std_formatter s then ()
  else (Format.print_string("Error in included file "^s);
        Format.print_newline());;

let (store_read_result,begin_load,end_load,get_libs) = let libs = ref []
  and stack = ref (Stack.create ())
  and known = ref (Hashtbl.create 10)
  and bnds_size = ref 0 in
  let _read = ref [] in
  let store_read_result s = _read := s
  and listify l = if l = [] then "[]"
    else "[\n"^(List.fold_right (fun a b -> a^";\n"^b) l "")^"\n]\n" in
  let file_of_string filename s =
    let fd = Pervasives.open_out filename in
      output_string fd s; close_out fd
  and pairnames = List.map (fun n -> "(\""^n^"\","^n^")") in
  let read_global_vals tns = let exptext =
      "store_read_result " ^ 
      (listify(pairnames tns))^
      ";;\n" in
     (let filename = Filename.temp_file "read_global_vals" ".ml" in
      file_of_string filename exptext;
      use_file filename;
      Sys.remove filename) in
  let map_new_syms lib = 
    let rec funpow n f x =
     if n < 1 then x else funpow (n-1) f (f x)
    and get_value_bindings env =
      let rec get_val acc = function
        | Env.Env_empty -> acc
        | Env.Env_value (next, ident, val_descr) ->
                get_val ((ident,val_descr)::acc) next
        | Env.Env_type (next,_,_) -> get_val acc next
        | Env.Env_exception (next,_,_) -> get_val acc next
        | Env.Env_module (next,_,_) -> get_val acc next
        | Env.Env_modtype (next,_,_) -> get_val acc next
        | Env.Env_class (next,_,_) -> get_val acc next
        | Env.Env_cltype (next,_,_) -> get_val acc next
        | Env.Env_open (next,_) -> get_val acc next
      in get_val [] (Env.summary env)
    and type_to_str (x : Types.type_expr) =
      Printtyp.type_expr Format.str_formatter x;
      Format.flush_str_formatter () in
    let pred = (fun (ident,val_descr) ->
        let n = Ident.name ident in
        if type_to_str val_descr.Types.val_type = "thm" & n <> "it"
        then true else false)
    and bnds = get_value_bindings (!Toploop.toplevel_env) in
    let new_bnds = funpow (!bnds_size) (List.tl) bnds in
    let new_ths = List.filter pred new_bnds in
    let new_th_names = List.map (fun (ident,_) -> Ident.name ident) new_ths in
    let lib_ths = Hashtbl.find (!known) lib in
      (Format.print_string("MAP SYMS - Stack:"^(if (not(Stack.is_empty (!stack))) then Stack.top (!stack) else "")^", lib: "^lib);
        Format.print_newline());
      bnds_size := List.length bnds;
      read_global_vals new_th_names;
      List.iter (fun (t,tv) -> Hashtbl.replace lib_ths t tv)
        (!_read);
      Hashtbl.replace (!known) lib lib_ths in
  let begin_load lib = if lib <> "/home/sternk/hol_light/fusion.ml" then
                        ((if (Stack.is_empty (!stack)) then ()
                        else
                          let plib = Stack.top (!stack)
                          in map_new_syms plib;
                             (Format.print_string("LIBLINK:"^lib);
                              Format.print_newline());
                            libs :=
                            (lib,plib)::(!libs));
                        (Format.print_string("Lib put on stack:"^lib);
                         Format.print_newline());
                        Stack.push lib (!stack);
                        Hashtbl.add (!known) lib (Hashtbl.create 10);
                        true) else false
  and end_load () = map_new_syms (Stack.pop (!stack))
  and get_libs () = let empty = Hashtbl.fold (fun k v t -> if Hashtbl.length v == 0 then k::t else t) (!known) []
                    and purge = fun names (h,l) -> (Hashtbl.fold (fun k v t -> (if List.mem k names then () else Hashtbl.add t k v); t) h (Hashtbl.create (Hashtbl.length h)),List.filter (fun (s,_) -> not(List.mem s names)) l)
                    and childnodes = fun n l -> List.fold_left (fun ch (s,t) -> if t == n || List.mem t ch then s::ch else ch) [] l
                    in let purgable = fun empty l -> List.filter (fun n ->
                                                     List.fold_left (fun b n1 -> b & (List.mem n1 empty)) true (childnodes n l)
                                                    ) empty
                    in purge (purgable empty (!libs)) (!known,!libs)
                     
  in
(*(Hashtbl.fold (fun k v t -> (if Hashtbl.length v > 0 then Hashtbl.add t k v else ()); t) (!known) (Hashtbl.create (Hashtbl.length (!known))), List.filter (fun (s,_) -> (Hashtbl.length (Hashtbl.find (!known) s)) > 0) (!libs)) in*)
  (store_read_result,begin_load,end_load,get_libs);

module Topdirs =
    struct
      (* type 'a printer_type_new = Format.formatter -> 'a -> unit
      type 'a printer_type_old = 'a -> unit *)
      let dir_quit = OldTopdirs.dir_quit
      let dir_directory = OldTopdirs.dir_directory
      let dir_cd = OldTopdirs.dir_cd
      let dir_load = fun f s -> if begin_load s then (OldTopdirs.dir_load f s; end_load()) else ()
      let dir_use = fun f s -> if begin_load s then (OldTopdirs.dir_use f s; end_load()) else ()
      let dir_install_printer = OldTopdirs.dir_install_printer
      let dir_remove_printer = OldTopdirs.dir_remove_printer
      let dir_trace = OldTopdirs.dir_trace
      let dir_untrace = OldTopdirs.dir_untrace
      let dir_untrace_all = OldTopdirs.dir_untrace_all
      let load_file = fun f s -> if begin_load s then let ret = OldTopdirs.load_file f s and _ = end_load() in ret else true
    end

module Toploop = 
    struct
      (*type directive_fun =
        Toploop.directive_fun =
          Directive_none  of (unit -> unit)
        | Directive_string of (string -> unit)
        | Directive_int of (int -> unit)
        | Directive_ident of (Longident.t -> unit)
        | Directive_bool of (bool -> unit) *)
      let getvalue = OldToploop.getvalue
      let setvalue = OldToploop.setvalue
      let set_paths = OldToploop.set_paths
      let loop = OldToploop.loop
      let run_script = OldToploop.run_script
      let directive_table = OldToploop.directive_table
      let toplevel_env = OldToploop.toplevel_env
      let initialize_toplevel_env = OldToploop.initialize_toplevel_env
      let print_exception_outcome = OldToploop.print_exception_outcome
      let execute_phrase = OldToploop.execute_phrase
      let use_file = fun f s -> if begin_load s then let ret = OldToploop.use_file f s and _ = end_load() in ret else true
      let use_silently = fun f s -> if begin_load s then let ret = OldToploop.use_silently f s and _ = end_load in ret else true
      let eval_path = OldToploop.eval_path
      let print_value = OldToploop.print_value
      let print_untyped_exception = OldToploop.print_untyped_exception
      let install_printer =  OldToploop.install_printer
      let remove_printer = OldToploop.remove_printer
      let max_printer_depth = OldToploop.max_printer_depth
      let max_printer_steps = OldToploop.max_printer_steps
      let parse_toplevel_phrase = OldToploop.parse_toplevel_phrase
      let parse_use_file = OldToploop.parse_use_file
      let print_location = OldToploop.print_location
      let print_error = OldToploop.print_error
      let print_warning = OldToploop.print_warning
      let input_name = OldToploop.input_name
      let print_out_value = OldToploop.print_out_value
      let print_out_type = OldToploop.print_out_type
      let print_out_class_type = OldToploop.print_out_class_type
      let print_out_module_type = OldToploop.print_out_module_type
      let print_out_sig_item = OldToploop.print_out_sig_item
      let print_out_signature = OldToploop.print_out_signature
      let print_out_phrase = OldToploop.print_out_phrase
      let read_interactive_input = OldToploop.read_interactive_input
      let toplevel_startup_hook = OldToploop.toplevel_startup_hook
      let may_trace = OldToploop.may_trace
    end

let use_file s =
  if Toploop.use_file Format.std_formatter s then ()
  else (Format.print_string("Error in included file "^s);
        Format.print_newline());;
