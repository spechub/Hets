(* 
Description :  Functions faciliating exporting theorems from HOL Light to HETS. Theorem database generation adapted from Examples/update_database.ml
               in the hol light source code distribution.

Copyright   :  (c) Jonathan von Schroeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt - for original license see 
               LICENSE txt in this directory or the HOL Light
               source distribution

Maintainer  :  jonathan.von_schroeder@dfki.de
Stability   :  experimental

 *)

(* !!!!!!! You must set this to point at the source directory in
   !!!!!!! which OCaml was built. (And don't do "make clean" beforehand.)
 
  the provided value is an example that works with a standard ocaml installation (aptitude install ocaml) on ubuntu

 *)

let ocaml_source_dir = "/usr/lib/ocaml/compiler-libs/";;

let sentences = ref ([]:(string*term)list);;

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

(* ------------------------------------------------------------------------- *)
(* Get the toplevel environment as raw data.                                 *)
(* ------------------------------------------------------------------------- *)

let get_value_bindings env =
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
  in get_val [] (Env.summary env);;

(* ------------------------------------------------------------------------- *)
(* Convert a type to a string, for ease of comparison.                       *)
(* ------------------------------------------------------------------------- *)

let type_to_str (x : Types.type_expr) =
  Printtyp.type_expr Format.str_formatter x;
         Format.flush_str_formatter ();;

(* ------------------------------------------------------------------------- *)
(* Remove bindings in first list from second assoc list (all ordered).       *)
(* ------------------------------------------------------------------------- *)

let rec demerge s l =
  match (s,l) with
    u::t,(x,y as p)::m ->
        if u = x then demerge t m
        else if u < x then demerge t l
        else p::(demerge s m)
  | _ -> l;;

(* ------------------------------------------------------------------------- *)
(* Incrementally update database.                                            *)
(* ------------------------------------------------------------------------- *)

let update_database =
  let uinfo = ((ref 0, ref undefined), (ref 0, ref undefined)) in
  let listify l = if l = [] then "[]"
                  else "[\n"^end_itlist (fun a b -> a^";\n"^b) l^"\n]\n" in
  let purenames = map (fun n -> "\""^n^"\"")
  and pairnames = map (fun n -> "\""^n^"\","^n) in
  let update_database' tstr vname value_bindings_checked theorem_bindings_existing = 
    let old_count = !value_bindings_checked
    and old_ths = !theorem_bindings_existing in
    let all_bnds = get_value_bindings (!Toploop.toplevel_env) in
    let new_bnds = funpow old_count tl all_bnds in
    let new_count = old_count + length new_bnds
    and new_ths =
      rev_itlist (fun (ident,val_descr) ->
        let n = Ident.name ident in
        if type_to_str val_descr.Types.val_type = tstr & n <> "it"
        then (n |-> ()) else undefine n) new_bnds old_ths in
    value_bindings_checked := new_count;
    if new_ths = old_ths then () else
    (print_string "Updating search database\n";
     theorem_bindings_existing := new_ths;
     let all_ths = combine (fun _ _ -> ()) (fun _ -> false) old_ths new_ths in
     let del_ths = combine (fun _ _ -> ()) (fun _ -> true) all_ths new_ths
     and add_ths = combine (fun _ _ -> ()) (fun _ -> true) all_ths old_ths in
     let del_names = mergesort (<) (foldr (fun a _ l -> a::l) del_ths [])
     and add_names = mergesort (<) (foldr (fun a _ l -> a::l) add_ths []) in
     let exptext =
      vname ^ " :=\n merge (increasing fst) (demerge "^
      (listify(purenames del_names))^
      " (!"^vname^")) "^
      (listify(pairnames add_names))^
      ";;\n" in
     (let filename = Filename.temp_file "database" ".ml" in
      file_of_string filename exptext;
      loadt filename;
      Sys.remove filename)) in
   fun () ->
      update_database' "thm" "theorems" (fst (fst uinfo)) (snd (fst uinfo));
      update_database' "term" "sentences" (fst (snd uinfo)) (snd (snd uinfo));;

let search' selector ts t = let filter_exp = can (term_match [] t) in
                            let sel = filter_exp o selector o snd in
                            let matching = filter sel ts in
                            try Some (List.hd matching) with
                            Failure _ -> None;;

let search_theorem t = search' concl (!theorems) t;;

let search_term t = let id x =x in search' id (!sentences) t;;

type sentence = { id : int ; axiom : bool ; incoming : int list ; tname : string };;

let dummy_sentence = { id=0 ; axiom = true; incoming = []; tname = ""};;

let (export,export_all) = let is_axiom th = let p = can (term_match [] (concl th)) in
                                     exists p (hyp th)
                   and fresh_id = let id = ref 0 in
                                  fun () ->
                                  id := (!id)+1;
                                  (!id) in
                  let insert sens th thn = let i = fresh_id() in 
                                      Hashtbl.add sens (concl th)
                                    { id = i; axiom = is_axiom th; tname = thn; 
                                      incoming = map (fun x -> let s = Hashtbl.find sens x in s.id) (filter ((<>)(concl th)) (hyp th)); } in
                  let hashtbl_to_list htbl = Hashtbl.fold (fun k v l -> (k,v)::l) htbl [] in
                  let rec expand sens th tname = 
                    let rec expand_sen sens tm = match search_theorem tm with
                                              Some (tname,th) -> expand sens th tname
                                            | None -> match search_term tm with
                                                        Some (tname,t) -> Hashtbl.remove sens tm;
                                                                          Hashtbl.add sens t
                                                        { id = fresh_id(); axiom = true;
                                                          incoming = []; tname = tname }
                                                      | None -> Hashtbl.replace sens tm 
                                                        { id = fresh_id(); axiom = true;
                                                         incoming = []; tname = "" }
                    and hashtbl_contains = Hashtbl.mem sens in
                    let tms = filter (not o hashtbl_contains) (hyp th) in
                    map (fun x -> Hashtbl.add sens x dummy_sentence) tms;
                    insert sens th tname;
                    map (expand_sen sens) tms;
                    () in
                  let e = fun tname ->
                       let t = (snd o List.hd) (filter (((=)tname) o fst) (!theorems))
                       and sens = Hashtbl.create ((List.length (!theorems))/10) in
                        expand sens t tname;
                        hashtbl_to_list sens
                   and e_a = fun () ->
                       let sens = Hashtbl.create (List.length (!theorems)) in
                        map (fun x -> if (((Hashtbl.mem sens) o concl o snd) x) then ()
                         else expand sens (snd x) (fst x)
                         ) (!theorems);
                        hashtbl_to_list sens in
                   (e,e_a);;

let get_parse_type fmt s =
  if is_prefix s then Format.fprintf fmt "Prefix"
  else if can get_infix_status s then
         match get_infix_status s with
                (i,"right") -> Format.fprintf fmt "(InfixR %u)" i
              | (i,"left") -> Format.fprintf fmt "(InfixL %u)" i
              | _ -> Format.fprintf fmt "Normal"
  else if parses_as_binder s then Format.fprintf fmt "Binder"
  else Format.fprintf fmt "Normal"

let get_term_info fmt (s0,ty0) = try let s = fst(find (fun (s,(s',ty)) -> s' = s0 & can (type_match ty ty0) []) (!the_interface))
                                 in Format.fprintf fmt "(HolTermInfo (%a,Just (%S,%a)))" get_parse_type s0 s get_parse_type s
                             with Failure _ -> Format.fprintf fmt "(HolTermInfo (%a,Nothing))" get_parse_type s0

let pp_d fmt =
                      let rec pp_list pp_el fmt = function
		        | [h] -> Format.fprintf fmt "%a" pp_el h
			| h::t ->
			   Format.fprintf fmt "%a%s@,%a"
			   pp_el h ", " (pp_list pp_el) t
			| [] -> ()
                      and pp_bool fmt x = Format.fprintf fmt "%s" (if x then "True" else "False") in
	              let rec pp_hol_type fmt = function
                        | Tyvar s -> Format.fprintf fmt "(TyVar %S)" s
			| Tyapp (s,ts) -> Format.fprintf fmt "(TyApp %S [%a])" s (pp_list pp_hol_type) ts in
                      let rec pp_term fmt = function
                        | Var (s,h) -> Format.fprintf fmt "Var %S (%a) %a" s pp_hol_type h get_term_info (s,h)
		        | Const (s,h) -> Format.fprintf fmt "Const %S (%a) %a" s pp_hol_type h get_term_info (s,h)
		        | Comb (t1,t2) -> Format.fprintf fmt "Comb (%a) (%a)" pp_term t1 pp_term t2
		        | Abs (t1,t2) -> Format.fprintf fmt "Abs (%a) (%a)" pp_term t1 pp_term t2 in
                      let pp_str_term_tuple fmt (s,t) = Format.fprintf fmt "(%S, %a)" s pp_term t in
                      let pp_op_map fmt (s,ts) = Format.fprintf fmt "(%S, [%a])" s (pp_list pp_hol_type) ts  in
                      let pp_data (ts,ops,sens) = Format.fprintf fmt "@[<h>([%a], [%a], [%a])@]" (pp_list pp_hol_type) ts (pp_list pp_op_map) ops (pp_list pp_str_term_tuple) sens in 
                    pp_data;;

(* this file needs to be imported right after all definitions that should not be exported have been loaded *)

let old_constants = ref([]:string list);;
if length (!old_constants) = 0 then
  old_constants := map fst (constants())
else ();;
let old_types = ref([]:string list);;
if length (!old_types) = 0 then
  old_types := map fst (types())
else ();;

let export_sig_sen () = let sens = map (fun (n,t) -> (n,concl t)) (!theorems) in
                     let sens_size = List.length sens in
                     let types = Hashtbl.create sens_size in
                     let ops = Hashtbl.create sens_size in
                     let htbl_to_list htbl f = Hashtbl.fold (fun k v l -> (f k v)::l) htbl [] in
                     let in_types = Hashtbl.mem types in
                     let rec get_primitive_types t =
                      if (match t with
                        Tyvar s -> not (mem s (!old_types))
                       |Tyapp (s,[]) -> not (mem s (!old_types))
                       |Tyapp (s,ts) -> List.map get_primitive_types ts; false) then if in_types t then () else Hashtbl.add types t 0
                      else () in 
                     let rec get_types ignore not_abs = function
                      | Var (s,t) -> get_primitive_types t;
                                     if not_abs & not (List.mem s ignore) & not (mem s (!old_constants)) then
                                       let tmap = if Hashtbl.mem ops s then Hashtbl.find ops s
                                                  else Hashtbl.create 1
                                       in Hashtbl.replace tmap t 0;Hashtbl.replace ops s tmap
                                     else ()
                      | Const (s,t) -> get_primitive_types t;
                                       if not (mem s (!old_constants)) then
                                         let tmap = if Hashtbl.mem ops s then Hashtbl.find ops s
                                                    else Hashtbl.create 1
                                         in Hashtbl.replace tmap t 0;Hashtbl.replace ops s tmap
                                       else ()
                      | Comb (t1,t2) -> get_types ignore true t1; get_types ignore true t2
                      | Abs (t1,t2) -> get_types ((name_of t1)::ignore) false t1; get_types ((name_of t1)::ignore) true t2 in
                     let _ = map ((get_types [] true) o snd) sens in
                     (htbl_to_list types (fun k _ -> k),htbl_to_list ops (fun k v -> (k,htbl_to_list v (fun k' _ -> k'))),sens);;

let export_sig_sen_to_file fname = let out_ch = open_out fname in
                               let fmt = Format.formatter_of_out_channel out_ch in
                               pp_d fmt (export_sig_sen());
                               close_out out_ch;;

theorems := [];;
sentences := [];;

update_database();;
