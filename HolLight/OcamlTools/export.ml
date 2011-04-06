#load "str.cma";;
let replace f = Str.global_replace (Str.regexp_string f)

let xml_escape_str s = replace "<" "&lt;"
 (replace "&" "&amp;"
 (replace ">" "&gt;"
 (replace "\"" "&quot;"
 (replace "'" "&apos;" s))))

let pp_str fmt s = Format.fprintf fmt "%s" (xml_escape_str s)

let pp_inner_indented s e pi fmt i = Format.fprintf fmt "@[<hv>@[<hv 1>%s@,%a@]@,@]%s" s pi i e

let pp_inner_tuple p1 p2 fmt (_1,_2) = Format.fprintf fmt "%a@,%a" (pp_inner_indented "<fst>" "</fst>" p1) _1 (pp_inner_indented "<snd>" "</snd>" p2) _2
let pp_tuple p1 p2 fmt t = pp_inner_indented "<tuple>" "</tuple>" (pp_inner_tuple p1 p2) fmt t

let pp_parse_type fmt s =
  if is_prefix s then Format.fprintf fmt "<Prefix />"
  else if can get_infix_status s then
         match get_infix_status s with
                (i,"right") -> Format.fprintf fmt "<InfixR>%u</InfixR>" i
              | (i,"left") -> Format.fprintf fmt "<InfixL>%u</InfixL>" i
              | _ -> Format.fprintf fmt "<Normal />"
  else if parses_as_binder s then Format.fprintf fmt "<Binder />"
  else Format.fprintf fmt "<Normal />"

let pp_term_info fmt (s0,ty0) = try let s = fst(find (fun (s,(s',ty)) -> s' = s0 & can (type_match ty ty0) []) (!the_interface))
                                 in Format.fprintf fmt "@[<v>%a@,%a@]" pp_parse_type s0 (pp_tuple pp_str pp_parse_type) (s,s)
                             with Failure _ -> Format.fprintf fmt "@[<h>%a@]" pp_parse_type s0

let rec pp_list pp_el fmt = function
 | [h]  -> Format.fprintf fmt "%a" pp_el h
 | h::t -> Format.fprintf fmt "%a@,%a" pp_el h (pp_list pp_el) t
 | []   -> ()

let rec pp_hol_type fmt = function
 | Tyvar s      -> pp_inner_indented "<TyVar>" "</TyVar>" pp_str fmt s
 | Tyapp (s,ts) -> pp_inner_indented "<TyApp>" "</TyApp>" (fun fmt (s,ts) -> Format.fprintf fmt "%a@,%a" pp_str s (pp_list pp_hol_type) ts) fmt (s,ts)

let rec pp_term fmt = function
 | Var (s,h)    -> pp_inner_indented "<Var>" "</Var>" (fun fmt (s,h) -> Format.fprintf fmt "%a@,%a@,%a" pp_str s pp_hol_type h pp_term_info (s,h)) fmt (s,h)
 | Const (s,h)  -> pp_inner_indented "<Const>" "</Const>" (fun fmt (s,h) -> Format.fprintf fmt "%a@,%a@,%a" pp_str s pp_hol_type h pp_term_info (s,h)) fmt (s,h)
 | Comb (t1,t2) -> pp_inner_indented "<Comb>" "</Comb>" (fun fmt (t1,t2) -> Format.fprintf fmt "%a@,%a" pp_term t1 pp_term t2) fmt (t1,t2)
 | Abs (t1,t2)  -> pp_inner_indented "<Abs>" "</Abs>" (fun fmt (t1,t2) -> Format.fprintf fmt "%a@,%a" pp_term t1 pp_term t2) fmt (t1,t2)

let pp_libs = pp_inner_indented "<Libs>" "</Libs>" (pp_list (pp_tuple pp_str (pp_list (pp_tuple pp_str pp_term))))
let pp_liblinks = pp_inner_indented "<LibLinks>" "</LibLinks>" (pp_list (pp_tuple pp_str pp_str))
let pp_export fmt (k,l) = pp_inner_indented "<HolExport>" "</HolExport>" (fun fmt (k,l) -> Format.fprintf fmt "%a@,%a" pp_libs k pp_liblinks l) fmt (k,l)

let print_to_file printer obj fname =
 let out_ch = open_out fname in
 let fmt = Format.formatter_of_out_channel out_ch in
 printer fmt obj;
 close_out out_ch;;

let htbl_to_list htbl f = Hashtbl.fold (fun k v l -> (f k v)::l) htbl [];;

let export_libs (h,l) f = print_to_file pp_export (htbl_to_list h (fun k v -> (k,htbl_to_list v (fun k1 v1 -> (k1,concl v1)))),("hol.ml",f)::l) f;;
