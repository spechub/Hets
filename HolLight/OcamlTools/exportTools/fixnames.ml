let char_list_to_string s' = let len = List.length s' in
                             let s   = String.create len in
                             (for i = 0 to pred len do
                               s.[i] <- List.nth s' i
                              done;
                              s);;

let rec string_to_char_list s = if String.length s = 0
 then []
 else s.[0] :: (string_to_char_list (String.sub s 1 ((String.length s)-1)));;

let rec nextName n = List.rev (match (List.rev n) with
         | []     -> ['a']
         | (x::xs) -> if (Char.code x) >= 122
                      then 'a'::(nextName xs)
                      else (Char.chr (succ (Char.code x)))::xs)

let freeName pref ns = let free = ref ((string_to_char_list pref)@['a']) in
 while List.exists ((=) (char_list_to_string (!free))) ns do
  free := nextName (!free)
 done;
 (char_list_to_string !free);;

let rec getNames t = match t with
 | Var   (s,_)   -> [s]
 | Const (s,_)   -> [s]
 | Comb  (t1,t2) -> (getNames t1)@(getNames t2)
 | Abs   (t1,t2) -> (getNames t1)@(getNames t2);;

let addTpName tbl ns n tp = try (
   let stbl = Hashtbl.find tbl n in
   try Hashtbl.find stbl tp 
   with Not_found -> 
   (let newName = freeName n (!ns) in
     ns := newName::(!ns);
     Hashtbl.add stbl tp newName; newName))
  with Not_found -> let stbl = Hashtbl.create 10 in
   (Hashtbl.add stbl tp n; Hashtbl.add tbl n stbl; n);;

let rec doRenames tbl ns t = match t with
 | Var   (s,tp)  -> let s' = addTpName tbl ns s tp in
                     mk_var (s',tp)
 | Const (s,tp)  -> t
 | Comb  (t1,t2) -> mk_comb (doRenames tbl ns t1,doRenames tbl ns t2)
 | Abs   (t1,t2) -> mk_abs (doRenames tbl ns t1,doRenames tbl ns t2)

let renameClashes t = doRenames (Hashtbl.create 100) (ref (getNames t)) t

let fixNames (s,t) = (s,renameClashes (concl t));;
