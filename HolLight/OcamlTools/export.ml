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
			| [] -> () in
	              let rec pp_hol_type fmt = function
                        | Tyvar s -> Format.fprintf fmt "TyVar %S" s
			| Tyapp (s,ts) -> Format.fprintf fmt "TyApp %S [%a]" s (pp_list pp_hol_type) ts in
                      let rec pp_term fmt = function
                        | Var (s,h) -> Format.fprintf fmt "Var %S (%a) %a" s pp_hol_type h get_term_info (s,h)
		        | Const (s,h) -> Format.fprintf fmt "Const %S (%a) %a" s pp_hol_type h get_term_info (s,h)
		        | Comb (t1,t2) -> Format.fprintf fmt "Comb (%a) (%a)" pp_term t1 pp_term t2
		        | Abs (t1,t2) -> Format.fprintf fmt "Abs (%a) (%a)" pp_term t1 pp_term t2 in
                      let pp_str_term_tuple fmt (s,t) = Format.fprintf fmt "(%S, %a)" s pp_term t in
                      let pp_str_types_tuple fmt (s,ts) = Format.fprintf fmt "(%S,[%a])" s (pp_list pp_hol_type) ts in
                      let pp_sig fmt (ts,ops) = Format.fprintf fmt "([%a],[%a])" (pp_list pp_hol_type) ts (pp_list pp_str_types_tuple) ops in
                      let pp_lib fmt (lname,ts,s) = Format.fprintf fmt "(%S,[%a],%a)" lname (pp_list pp_str_term_tuple) ts pp_sig s in
                      let pp_str_tuple fmt (s1,s2) = Format.fprintf fmt "(%S, %S)" s1 s2 in
                      let pp_data (ts,l) = Format.fprintf fmt "@[<h>([%a], [%a])@]" (pp_list pp_lib) ts (pp_list pp_str_tuple) l in 
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

let export_sig_sen (s,l) =
                     let types = Hashtbl.create 10 in
                     let ops = Hashtbl.create 10 in
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
                     ((htbl_to_list s (fun k v ->
                        let sens = htbl_to_list v (fun k' v' -> (k',concl v')) in
                        let _ = List.map ((get_types [] true) o snd) sens in
                        let l = (htbl_to_list types (fun k _ -> k),htbl_to_list ops (fun k v -> (k,htbl_to_list v (fun k' _ -> k')))) in
                          Hashtbl.clear types;
                          Hashtbl.clear ops;
                          (k,sens,l))),l)
                     ;;

let export_sig_sen_to_file s fname = let out_ch = open_out fname in
                               let fmt = Format.formatter_of_out_channel out_ch in
                               pp_d fmt (export_sig_sen s);
                               close_out out_ch;;
