{- |
Module      :  $Header$
Copyright   :  (c) University of Cambridge, Cambridge, England
               adaption (c) Till Mossakowski, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   translate 'Id' to Isabelle strings
-}

module Isabelle.Translate (showIsa, showIsaT, showIsaSid, showIsaI, showIsaIT, replaceChar, transString) where

import Common.Id 
import qualified Common.Lib.Map as Map
import Data.Char
import Data.Maybe
import Debug.Trace
import Isabelle.IsaSign

------------------- Id translation functions -------------------
isaPrelude :: [(IName,[String])]
isaPrelude = [("MainHC",["pApp","apt","app","defOp","pair"]),

  ("Pure",["!!","#prop","==","==>","=?=","Goal","TYPE",
  "_DDDOT","_K","_TYPE","_abs","_appl","_aprop","_args","_asms",
  "_bigimpl","_bracket","_classes","_constify","_constrain",
  "_dummy_ofsort","_idts","_idtyp","_index","_indexvar","_lambda",
  "_meta_conjunction","_mk_ofclass","_noindex","_ofclass","_ofsort","_pttrns","_sort",
  "_struct","_tapp","_tappl","_topsort","_types","all","any","aprop","args","asms","cargs",
  "classes","dummy","dummy_pattern","fun","id","idt","idts",
  "index","itself","logic","logic_class","longid","num","num_const","prop","pttrn",
  "pttrns","sort","struct","tid","tvar","type","types","var","xnum","xstr"]),

  ("HOL",["!!","!!","#prop","0","1","==","==>","=?=","ALL ","All","EX ","EX! ","Ex","Ex1","False",
  "Goal","If","LEAST ","Least","Let","Not","TYPE","The","True","Trueprop",
  "_DDDOT","_K","_Let","_TYPE","_The","_abs","_appl","_applC","_aprop","_args","_asms",
  "_bigimpl","_bind","_binds","_bracket","_cargs","_case1",
  "_case2","_case_syntax","_classes","_constify","_constrain","_dummy_ofsort",
  "_idts","_idtyp","_index","_index1","_indexvar","_lambda",
  "_leAll","_leEx","_lessAll",
  "_lessEx","_meta_conjunction","_mk_ofclass","_noindex",
  "_not_equal","_ofclass","_ofsort",
  "_pttrns","_sort","_struct","_tapp","_tappl","_topsort","_types","abs",
  "all","any","aprop","arbitrary","args","asms","bool","cargs","case_syn","classes",
  "divide","dummy","dummy_pattern","fun","id","idt","idts",
  "index","induct_conj","induct_equal","induct_forall","induct_implies","inverse",
  "inverse_class","itself","letbind","letbinds","linorder","linorder_class","logic",
  "logic_class","longid","max","min","minus","minus_class","mono","num","num_const","one",
  "one_class","op &","op *","op +","op -","op -->","op <","op <=", 
  "op =","op |","ord","ord_class","order",
  "order_class","plus","plus_class","prop","pttrn","pttrns","sort","struct","tid","times",
  "times_class","tvar","type","type","type_class","types","uminus","var","xnum","xstr","zero",
  "zero_class"]),

  ("Main",["!!","#prop","*","+","0","1","==", "==>","=?=","@Coll","@Finset","@INTER","@INTER1",
  "@INTER_le", "@INTER_less","@SetCompr","@Sigma","@Times","@UNION","@UNION1","@UNION_le",
  "@UNION_less","@chg_map","@filter","@list","ACe","ALL","Abs_Integ","Abs_Nat","Abs_Node",
  "Abs_Prod","Abs_Sum","Abs_bin","Abs_char","Abs_list","Abs_nibble","Abs_option","Abs_sumbool",
  "Abs_unit","All","Alm_all","Atom","Ball","Bex","Bit","Case","Char","Collect","Cons","Domain",
  "EX ","EX! ","Eps","Ex","Ex1","False","Field","Finites","GREATEST ","Goal","Greatest",
  "GreatestM","INF ","INTER","Id","If","Image","In0","In1","Inf_many","Inl","Inl_Rep","Inr",
  "Inr_Rep","Integ","Inter","Ints","Inv","LC","LEAST ","Leaf","Least","LeastM","Left","Let",
  "Lim","MOST ","Max","Min","NCons","Nat","Nats","Nibble0","Nibble1","Nibble2","Nibble3",
  "Nibble4","Nibble5","Nibble6","Nibble7","Nibble8","Nibble9","NibbleA","NibbleB","NibbleC",
  "NibbleD","NibbleE","NibbleF","Nil","Node","None","Not","Numb","Numeral0","Numeral1","Pair",
  "Pair_Rep","Part","Pls","Plus","Pow","Prod","Push","Push_Node","Range","Rep_Integ","Rep_Nat",
  "Rep_Node","Rep_Prod","Rep_Sum","Rep_bin","Rep_char","Rep_list","Rep_nibble","Rep_option",
  "Rep_sumbool","Rep_unit","Right","Scons","Sigma","Some","Split","Suc","Suc_Rep","Sum","Suml",
  "Summation","Sumr","TYPE","The","True","Trueprop","UNION","UNIV","Union","Unity","Zero_Rep",
  "_Ball","_Bex","_Char","_DDDOT","_Eps","_GreatestM","_K","_LUpdate","_LeastM","_Let","_Map",
  "_MapUpd","_Maplets","_Numeral","_String","_Summation","_TYPE","_The","_Update","_abs","_appl",
  "_applC","_aprop","_args","_asms","_bigimpl","_bind","_binds","_bracket","_cargs","_case1",
  "_case2","_case_syntax","_classes","_constify","_constrain","_dummy_ofsort","_field",
  "_field_type","_field_types","_fields","_idts","_idtyp","_index","_index1","_indexvar",
  "_lambda","_leAll","_leEx","_lessAll","_lessEx","_lupdbind","_lupdbinds","_maplet","_maplets",
  "_meta_conjunction","_mk_ofclass","_noindex","_not_equal","_ofclass","_ofsort","_pattern",
  "_patterns","_pttrns","_record","_record_scheme","_record_type","_record_type_scheme",
  "_record_update","_reflcl","_setle","_setless","_setprod","_setsum","_sort","_square",
  "_struct","_tapp","_tappl","_topsort","_tuple","_tuple_arg","_tuple_args","_types","_update",
  "_update_name","_updates","_updbind","_updbinds","abelian_group","abelian_group_class",
  "abelian_semigroup","abelian_semigroup_class","abs","acyclic","adjust","adm_wf","all",
  "almost_ordered_semiring","almost_ordered_semiring_class","almost_semiring",
  "almost_semiring_class","antisym","any","apfst","aprop","arbitrary","args","asms","atLeast",
  "atLeastAtMost","atLeastLessThan","atMost","atmost_one","bij","bin","bin_add","bin_case",
  "bin_minus","bin_mult","bin_pred","bin_rec","bin_rec_set","bin_rep_set","bin_succ","binomial",
  "bool","bool_case","bool_rec","bool_rec_set","butlast","card","cardR","cargs","case_syn",
  "cases_syn","char","char_case","char_rec","char_rec_set","char_rep_set","chg_map","classes",
  "comp","concat","congruent","congruent2","contents","converse","curry","cut","diag","distinct",
  "div","divAlg","div_class","divide","division_by_zero","division_by_zero_class","dom","dprod",
  "drop","dropWhile","dsum","dtree","dummy","dummy_pattern","empty","equiv","even","even_odd",
  "even_odd_class","field","field_class","field_type","field_types","fields","filter","finite",
  "finite_class","finite_psubset","fold","foldSet","foldl","foldr","fst","fun","fun_upd","gfp",
  "greaterThan","greaterThanAtMost","greaterThanLessThan","hd","id","ident","idt","idts","image",
  "ind","index","induct_conj","induct_equal","induct_forall","induct_implies","infinite","inj",
  "inj_on","insert","int","int_aux","internal_split","intrel","inv","inv_image","inverse",
  "inverse_class","iszero","item","itself","last","length","lessThan","less_than","letbind",
  "letbinds","lex","lex_prod","lexico","lexn","lfp","linorder","linorder_class","list",
  "list_all","list_all2","list_case","list_rec","list_rec_set","list_rep_set","list_update",
  "lists","logic","logic_class","longid","lupdbind","lupdbinds","map","map_add","map_image",
  "map_le","map_of","map_subst","map_upd_s","map_upds","maplet","maplets","max","measure","min",
  "minus","minus_class","mono","myinv","nat","nat_aux","nat_case","nat_rec","nat_rec_set",
  "ndepth","neg","negDivAlg","negateSnd","nibble","nibble_case","nibble_rec","nibble_rec_set",
  "nibble_rep_set","node","nth","ntrunc","null","num","num_const","number","number_class",
  "number_of","number_ring","number_ring_class","o2s","odd","of_int","of_nat","one","one_class",
  "&","*","+","-","->",":","<","<=","=","@","Int","Un",
  "div","dvd","mem","mod","|","~:","option","option_case","option_map",
  "option_rec","option_rec_set","option_rep_set","ord","ord_class","order","order_class",
  "ordered_field","ordered_field_class","ordered_ring","ordered_ring_class","ordered_semiring",
  "ordered_semiring_class","overwrite","patterns","plus","plus_ac0","plus_ac0_class",
  "plus_class","posDivAlg","power","power_class","pred_nat","prod_case","prod_fun","prod_rec",
  "prod_rec_set","product_type","prop","pttrn","pttrns","quorem","quotient","ran","range","refl",
  "reflexive","rel_comp","remdups","replicate","restrict_map","rev","ring","ring_class",
  "ringpower","ringpower_class","rtrancl","same_fst","semiring","semiring_class","set","setprod",
  "setsum","single_valued","size","snd","sort","split","string","struct","sublist","sum_case",
  "sum_rec","sum_rec_set","sumbool","sumbool_case","sumbool_rec","sumbool_rec_set",
  "sumbool_rep_set","surj","sym","take","takeWhile","the","tid","times","times_ac1",
  "times_ac1_class","times_class","tl","trancl","trans","tuple_args","tvar","type","type_class",
  "type_definition","types","uminus","unit","unit_case","unit_rec","unit_rec_set","upd_fst",
  "upd_snd","update","updates","updbind","updbinds","uprod","upt","upto","usum","var","vimage",
  "wellorder","wellorder_class","wf","wfrec","wfrec_rel","xnum","xstr","zero","zero_class","zip",
  "{}","~=>", "O", "o"])]

showIsa :: Id -> String
showIsa ident = trace "Please use 'showIsaT :: Id -> IName -> String' instead of showIsa." 
                      (showIsaT ident "Pure")

showIsaT :: Id -> IName -> String 
showIsaT ident theory =  
-- "stripUnderscores sident" was substided by sident because there is no problem, if reserved words
-- differ from sident only by underscrores
  if sident `elem` (selList isaPrelude theory) then sident++"X" else sident
  where 
   sident = transString $ show ident

   selList [] _ = []
   selList ((l,list):ls) thy = if l == thy then list else selList ls thy

-- not in use
-- stripUnderscores :: String -> String
-- stripUnderscores = catMaybes . map (\c -> if c=='_' then Nothing else Just c)

showIsaSid :: SIMPLE_ID -> String
showIsaSid = transString . show

showIsaI :: Id -> Int -> String
showIsaI ident i = trace "Please use 'showIsaIT :: Id -> Int -> IName -> String' instead of showIsaI." 
                      (showIsaIT ident i "Pure")

showIsaIT :: Id -> Int -> IName -> String
showIsaIT ident i theory = showIsaT ident theory ++ "_" ++ show i

isIsaChar :: Char -> Bool
isIsaChar c = (isAlphaNum c && isAscii c) || c `elem` "_'"

replaceChar1 :: Char -> String
replaceChar1 c | isIsaChar c = [c] 
               | otherwise = replaceChar c++"X"

transString :: String -> String
transString "" = "X"
transString (c:s) = 
   if isInf (c:s) then concat $ map replaceChar1 (cut (c:s))
     else ((if isAlpha c && isAscii c then [c] 
              else 'X':replaceChar1 c) ++ (concat $ map replaceChar1 s))

isInf :: String -> Bool
isInf s = has2Under s && has2Under (reverse s)

has2Under :: String -> Bool
has2Under (fs:sn:_) = fs == '_' && sn == '_'
has2Under _ = False

cut :: String -> String
cut = reverse . tail . tail . reverse . tail . tail

-- Replacement of special characters

replaceChar :: Char -> String
replaceChar c = if isIsaChar c then [c] else 
                Map.findWithDefault "_" c $ Map.fromList 
 [('!' , "Exclam"),
  ('#' , "Sharp"),
  ('$' , "Dollar"),
  ('%' , "Percent"),
  ('&' , "Amp"),
  ('(' , "OBra"),
  (')' , "CBra"),
  ('*' , "x"),
  ('+' , "Plus"),
  (',' , "Comma"),
  ('-' , "Minus"),
  ('.' , "Dot"),
  ('/' , "Div"),
  (':' , "Colon"),
  (';' , "Semi"),
  ('<' , "Lt"),
  ('=' , "Eq"),
  ('>' , "Gt"),
  ('?' , "Q"),
  ('@' , "At"),
  ('\\' , "Back"),
  ('^' , "Hat"),
  ('`' , "'"),
  ('{' , "Cur"),
  ('|' , "Bar"),
  ('}' , "Ruc"),
  ('~' , "Tilde"),
  ('\128' , "A1"),
  ('\129' , "A2"),
  ('\130' , "A3"),
  ('\131' , "A4"),
  ('\132' , "A5"),
  ('\133' , "A6"),
  ('\134' , "AE"),
  ('\135' , "C"),
  ('\136' , "E1"),
  ('\137' , "E2"),
  ('\138' , "E3"),
  ('\139' , "E4"),
  ('\140' , "I1"),
  ('\141' , "I2"),
  ('\142' , "I3"),
  ('\143' , "I4"),
  ('\144' , "D1"),
  ('\145' , "N1"),
  ('\146' , "O1"),
  ('\147' , "O2"),
  ('\148' , "O3"),
  ('\149' , "O4"),
  ('\150' , "O5"),
  ('\151' , "x"),
  ('\152' , "O"),
  ('\153' , "U1"),
  ('\154' , "U2"),
  ('\155' , "U3"),
  ('\156' , "U4"),
  ('\157' , "Y"),
  ('\158' , "F"),
  ('\159' , "ss"),
  ('¡' , "SpanishExclam"),
  ('¢' , "c"),
  ('£' , "Lb"),
  ('¤' , "o"),
  ('¥' , "Yen"),
  ('¦' , "Bar1"),
  ('§' , "Paragraph"),
  ('¨' , "\'"),
  ('©' , "Copyright"),
  ('ª' , "a1"),
  ('«' , "\'"),
  ('¬' , "not"),
  ('­' , "Minus1"),
  ('®' , "Regmark"),
  ('°' , "Degree"),
  ('±' , "Plusminus"),
  ('²' , "2"),
  ('³' , "3"),
  ('´' , "'"),
  ('µ' , "Mu"),
  ('¶' , "q"),
  ('·' , "Dot"),
  ('¸' , "'"),
  ('¹' , "1"),
  ('º' , "2"),
  ('»' , "\'"),
  ('¼' , "Quarter"),
  ('½' , "Half"),
  ('¾' , "Threequarter"),
  ('¿' , "Q"),
  ('À' , "A7"),
  ('Á' , "A8"),
  ('Â' , "A9"),
  ('Ã' , "A10"),
  ('Ä' , "A11"),
  ('Å' , "A12"),
  ('Æ' , "AE2"),
  ('Ç' , "C2"),
  ('È' , "E5"),
  ('É' , "E6"),
  ('Ê' , "E7"),
  ('Ë' , "E8"),
  ('Ì' , "I5"),
  ('Í' , "I6"),
  ('Î' , "I7"),
  ('Ï' , "I8"),
  ('Ð' , "D2"),
  ('Ñ' , "N2"),
  ('Ò' , "O6"),
  ('Ó' , "O7"),
  ('Ô' , "O8"),
  ('Õ' , "O9"),
  ('Ö' , "O10"),
  ('×' , "xx"),
  ('Ø' , "011"),
  ('Ù' , "U5"),
  ('Ú' , "U6"),
  ('Û' , "U7"),
  ('Ü' , "U8"),
  ('Ý' , "Y"),
  ('Þ' , "F"),
  ('ß' , "ss"),
  ('à' , "a2"),
  ('á' , "a3"),
  ('â' , "a4"),
  ('ã' , "a5"),
  ('ä' , "a6"),
  ('å' , "a7"),
  ('æ' , "ae"),
  ('ç' , "c"),
  ('è' , "e1"),
  ('é' , "e2"),
  ('ê' , "e3"),
  ('ë' , "e4"),
  ('ì' , "i1"),
  ('í' , "i2"),
  ('î' , "i3"),
  ('ï' , "i4"),
  ('ð' , "d"),
  ('ñ' , "n"),
  ('ò' , "o1"),
  ('ó' , "o2"),
  ('ô' , "o3"),
  ('õ' , "o4"),
  ('ö' , "o5"),
  ('÷' , "Div1"),
  ('ø' , "o6"),
  ('ù' , "u1"),
  ('ú' , "u2"),
  ('û' , "u3"),
  ('ü' , "u4"),
  ('ý' , "y5"),
  ('þ' , "f"),
  ('ÿ' , "y")]
