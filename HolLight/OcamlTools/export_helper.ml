#load "str.cma";;
let replace f = Str.global_replace (Str.regexp_string f)

type sharedHolType = Styvar of int
                   | Styapp of int * (int list)

type sharedTerm = Svar of int * int * (string * hol_type)
                | Sconst of int * int * (string * hol_type)
                | Scomb of int * int
                | Sabs of int * int

let hol_strings = Hashtbl.create 1000
let shared_hol_types = Hashtbl.create 1000
let shared_hol_terms = Hashtbl.create 1000

let insertOrIdx htbl d = try Hashtbl.find htbl d
                     with Not_found -> let idx = (Hashtbl.length htbl) + 1
                      in Hashtbl.add htbl d idx; idx

let rec mkSharedHolType tp = match tp with
   Tyvar s     -> insertOrIdx shared_hol_types
                   (Styvar (insertOrIdx hol_strings s))
 | Tyapp (s,l) -> insertOrIdx shared_hol_types
                   (Styapp ((insertOrIdx hol_strings s),
                    (List.map mkSharedHolType l)))

let rec mkSharedTerm t = match t with
   Var (s,tp)   -> insertOrIdx shared_hol_terms
                   (Svar ((insertOrIdx hol_strings s),
                           mkSharedHolType tp,(s,tp)))
 | Const (s,tp) -> insertOrIdx shared_hol_terms
                   (Sconst ((insertOrIdx hol_strings s),
                           mkSharedHolType tp,(s,tp)))
 | Comb (t1,t2) -> insertOrIdx shared_hol_terms
                   (Scomb (mkSharedTerm t1, mkSharedTerm t2))
 | Abs (t1,t2)  -> insertOrIdx shared_hol_terms
                   (Sabs (mkSharedTerm t1, mkSharedTerm t2))

let xml_escape_str s = replace "<" "&lt;"
 (replace "'" "&apos;"
 (replace ">" "&gt;"
 (replace "\"" "&quot;"
 (replace "&" "&amp;" s))))

let pp_int fmt i = Format.fprintf fmt "%i" i

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

let rec pp_shared_hol_type fmt = function
 | Styvar s      -> pp_inner_indented "<TyVar>" "</TyVar>" pp_int fmt s
 | Styapp (s,ts) -> pp_inner_indented "<TyApp>" "</TyApp>" (pp_tuple pp_int (pp_list (pp_inner_indented "<i>" "</i>" pp_int))) fmt (s,ts)

let rec pp_shared_term fmt = function
 | Svar (s,h,t)    -> pp_inner_indented "<Var>" "</Var>" (fun fmt (s,h,t) -> Format.fprintf fmt "%a@,%a" (pp_tuple pp_int pp_int) (s,h) pp_term_info t) fmt (s,h,t)
 | Sconst (s,h,t)  -> pp_inner_indented "<Const>" "</Const>" (fun fmt (s,h,t) -> Format.fprintf fmt "%a@,%a" (pp_tuple pp_int pp_int) (s,h) pp_term_info t) fmt (s,h,t)
 | Scomb (t1,t2) -> pp_inner_indented "<Comb>" "</Comb>" (fun fmt (t1,t2) -> Format.fprintf fmt "%a" (pp_tuple pp_int pp_int) (t1,t2)) fmt (t1,t2)
 | Sabs (t1,t2)  -> pp_inner_indented "<Abs>" "</Abs>" (fun fmt (t1,t2) -> Format.fprintf fmt "%a" (pp_tuple pp_int pp_int) (t1,t2)) fmt (t1,t2)

let htbl_to_list htbl f = Hashtbl.fold (fun k v l -> (f k v)::l) htbl [];;

let sharedtbl_to_list tbl = List.sort (fun (v1,_) (v2,_) -> v1-v2) (htbl_to_list tbl (fun k v -> (v,k)))

let map_snd = List.map snd

let pp_shared_hol_type_snd fmt d = pp_shared_hol_type fmt (snd d) 
let pp_shared_term_snd fmt d = pp_shared_term fmt (snd d)

let pp_hol_strings fmt d = pp_inner_indented "<Strings>" "</Strings>" (pp_list (pp_inner_indented "<s>" "</s>" pp_str)) fmt (map_snd (sharedtbl_to_list d))
let pp_shared_hol_types fmt d = pp_inner_indented "<SharedHolTypes>" "</SharedHolTypes>" (pp_list pp_shared_hol_type_snd) fmt (sharedtbl_to_list d)
let pp_shared_hol_terms fmt d = pp_inner_indented "<SharedHolTerms>" "</SharedHolTerms>" (pp_list pp_shared_term_snd) fmt (sharedtbl_to_list d)

let pp_libs = pp_inner_indented "<Libs>" "</Libs>" (pp_list (pp_tuple pp_str (pp_list (pp_tuple pp_str pp_int))))
let pp_liblinks = pp_inner_indented "<LibLinks>" "</LibLinks>" (pp_list (pp_tuple pp_str pp_str))
let pp_export fmt (k,l) = pp_inner_indented "<HolExport>" "</HolExport>" (fun fmt (k,l) -> Format.fprintf fmt "%a@,%a@,%a@,%a@,%a" pp_hol_strings hol_strings pp_shared_hol_types shared_hol_types pp_shared_hol_terms shared_hol_terms pp_libs k pp_liblinks l) fmt (k,l)

let print_to_file printer obj fname =
 let out_ch = open_out fname in
 let fmt = Format.formatter_of_out_channel out_ch in
 printer fmt obj;
 close_out out_ch;;

let export_libs (h,l) f = print_to_file pp_export (htbl_to_list h (fun k v -> (k,htbl_to_list v (fun k1 v1 -> (k1,mkSharedTerm (concl v1))))),l) f;;
