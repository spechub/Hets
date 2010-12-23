{- |
Module      :  $Header$
Description :  Sentence for HolLight logic
Copyright   :  (c) Jonathan von Schroeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  jonathan.von_schroeder@dfki.de
Stability   :  experimental
Portability :  portable

Definition of sentences for HolLight logic

  Ref.

  <http://www.cl.cam.ac.uk/~jrh13/hol-light/>

-}
module HolLight.Sentence where

import Common.AS_Annotation
import Common.DocUtils
import HolLight.Sign()
import Common.Doc
import HolLight.Helper
import HolLight.Term
import Data.Maybe (fromJust,catMaybes,isNothing)
import qualified Data.Char as Char

data Sentence = Sentence {
  name :: String,
  term :: Term,
  proof :: Maybe HolProof
  } deriving (Eq, Ord, Show)

printNamedSen :: Named Sentence -> Doc
printNamedSen ns =
  let s = sentence ns
  in (hcat [text (name s), text " = `",
                    (pp_print_term . term) s,text "`"])


instance Pretty Sentence where
  pretty s = (hcat [text (name s), text " = `",
                    (pp_print_term . term) s,text "`"])

pp_print_term :: Term -> Doc
pp_print_term tm = print_term 0 tm

prec_parens :: Num a => a -> Doc -> Doc
prec_parens prec = if prec /= 0 then parens else id

replace_pt :: Term -> HolParseType -> Term
replace_pt tm pt = case tm of
  Var s t _ -> Var s t (HolTermInfo (pt,Nothing))
  Const s t _ -> Const s t (HolTermInfo (pt,Nothing))
  _ -> tm

print_term :: Int -> Term -> Doc
print_term prec tm =
 let _1 = case dest_numeral tm of
         Just i -> Just (text (show i))
         _ -> Nothing in
  let _2 = case dest_list tm of
         Just tms -> case type_of tm of
           Just t -> case dest_type t of
             Just (_,x:_) -> case dest_type x of
               Just ("char",_) -> let cs = map code_of_term tms
                 in if any isNothing cs then Nothing
                    else Just (quotes (text (foldr (:) []
                                              (map Char.chr (catMaybes cs)))))
               _ -> Nothing
             _ -> Nothing
           _ -> Nothing
         _ -> Nothing in
 let _3 = if isNothing _2 then case dest_list tm of
            Just tms -> Just (brackets (print_term_sequence "; " 0 tms))
            _ -> Nothing
       else Nothing in
 let _4 = if is_gabs tm then Just (print_binder prec tm)
       else Nothing in
 let (s,_,args,hop) = case strip_comb tm of
               (hop',args') -> case fromJust (type_of hop') of {- not really sure in which cases (type_of hop) == Nothing, but shouldn't happen if i understand the original ocaml code correctly-}
                  ty0' ->
                    let s0 = name_of hop' in
                    case reverse_interface (s0,hop') of
                      (s',Just pt) -> (s',ty0',args',replace_pt hop' pt)
                      _ -> (s0,ty0',args',hop') in
 let _5 = case (s,is_const tm,args==[]) of
         ("EMPTY",True,True) -> Just (braces empty)
         ("UNIV",True,True) -> case type_of tm of
            Just t -> case dest_fun_ty t of
              Just (ty,_) -> Just (parens (hcat [text ":",pp_print_type ty]))
              _ -> Nothing
            _ -> Nothing
         ("INSERT",_,_) ->
            let (mems,oth) = splitlist (dest_binary' "INSERT") tm
            in case (is_const oth, dest_const oth) of
                 (True,Just ("EMPTY",_)) -> Just (braces (print_term_sequence
                                                     ", " 14 mems))
                 _ -> Nothing
         ("GSPEC",_,_) -> case rand tm of
            Just rtm -> case body rtm of
              Just b -> let (evs,bod) = strip_exists b
                        in case dest_comb bod of
                             Nothing -> Nothing
                             Just (bod1,fabs) ->
                               case dest_comb bod1 of
                                 Nothing -> Nothing
                                 Just (bod2,babs) ->
                                   case rator bod2 of
                                     Nothing -> Nothing
                                     Just c ->
                                       case dest_const c of
                                         Just ("SETSPEC",_) -> Just (braces (hcat [
                                           print_term 0 fabs,
                                           text " | ",
                                           print_term_sequence "," 14 evs,
                                           text " | ",
                                           print_term 0 babs
                                          ]))
                                         _ -> Nothing
              _ -> Nothing
            _ -> Nothing
         _ -> Nothing in
 let _6 = case dest_let tm of
         Just (e:eqs,_) -> case mk_eq e of
           Just e' -> let eqs' = map (\(v,t) -> mk_eq (v,t)) eqs
             in if any ((==)Nothing) eqs' then Nothing else
                Just ((prec_parens prec)
                        (hcat [
                          text "let ",
                          print_term 0 e',
                          vcat ((map (\ eq -> hcat [
                               text "and ",
                               print_term 0 eq]) (catMaybes eqs'))
                                ++ [text " in",text ""])
                        ]))
           _ -> Nothing
         _ -> Nothing in
 let _7 = if s == "DECIMAL" then
         case (dest_numeral (args!!0), dest_numeral (args!!1)) of
           (Just n_num, Just n_den) -> if not(powerof10 n_den) then Nothing
             else let s_num = text (show (n_num `quot` n_den)) in
                  let s_den = text (concat (tail (map (\x -> [x])
                                    (show (n_den + (n_num `mod` n_den)))
                                   )))
                   in Just (hcat [text "#",s_num,(if n_den == 1 then empty
                                            else text "."),
                            s_den])
           _ -> Nothing
       else Nothing in
 let _8 = if s == "_MATCH" && length args == 2 then
         case dest_clauses(args!!1) of
           Just cls -> Just ((prec_parens prec) (vcat [
             hcat [text "match ",
              print_term 0 (args!!0),
              text " with"],
             print_clauses cls]))
           _ -> Nothing
       else Nothing in
 let _9 = if s == "_FUNCTION" && length args == 1 then
            case dest_clauses (head args) of
              Just cls -> Just ((prec_parens prec) (vcat [
                  text "function",
                  print_clauses cls
                ]))
              _ -> Nothing
          else Nothing in
 let _10 = if s == "COND" && length args == 3 then
         Just ((prec_parens prec) (vcat [
          hcat [text "if ",print_term 0 (args!!0)],
          hcat [text " then ",print_term 0 (args!!1)],
          hcat [text " else ",print_term 0 (args!!2)]
         ]))
       else Nothing in
 let _11 = if is_prefix hop && length args == 1 then
          Just ((if prec == 1000 then parens else id)
                (if (all Char.isAlphaNum s) || s == "--"
                    || (
                        case dest_comb (args!!0) of
                          Just (l,_) -> let (s0,_) = (name_of l,type_of l)
                            in fst(reverse_interface (s0,hop)) == "--"
                               || (case (dest_const l) of
                                    Just (f,_) -> elem f ["real_of_num",
                                                          "int_of_num"]
                                    _ -> False)
                          _ -> False)
                    || s == "~" then hcat [text s, print_term 999 (args!!0), text " "]
                 else hcat [text s, print_term 999 (args!!0)]))
        else Nothing in
 let _12 = if parses_as_binder hop && length args == 1 && is_gabs (args!!0)
           then Just (print_binder prec tm)
           else Nothing in
 let _13 = if can_get_infix_status hop && length args == 2 then
          let bargs = if aright hop then
                        let (tms,tmt) = splitlist (dest_binary hop) tm
                                         in tms++[tmt]
                      else
                        let (tmt,tms) = rev_splitlist (dest_binary hop) tm
                                         in tmt:tms in
          let (newprec,unspaced_binops) = (get_prec hop,[",","..","$"])
          in Just ((if newprec <= prec then parens else id) (hcat
                    (print_term newprec (bargs!!0):(
                     map (\x ->
                      if elem s unspaced_binops then hcat [text s,
                                                       print_term newprec x]
                      else hcat [text " ",text s,text " ",print_term newprec x]
                     ) (tail bargs)
                  ))))
        else Nothing in
 let _14 = if (is_const hop || is_var hop) && args == [] then
             let s' = if parses_as_binder hop || can_get_infix_status hop
                         || is_prefix tm then parens (text s) else text s
             in Just s'
           else Nothing in
 let _15 = case dest_comb tm of
              Just (l,r) -> let mem = case dest_const l of
                                        Just (s',_) -> elem s'
                                          ["real_of_num","int_of_num"]
                                        _ -> False
                            in Just ((if prec == 1000 then parens else id)
                                         (if not mem
                                          then hcat [print_term 999 l, text " ",
                                                     print_term 1000 r]
                                          else hcat [print_term 999 l,
                                                     print_term 1000 r]))
              _ -> Nothing
 in head (catMaybes [_1,_2,_3,_4,_5,_6,_7,_8,_9,
                     _10,_11,_12,_13,_14,_15,Just empty])

print_term_sequence :: [Char] -> Int -> [Term] -> Doc
print_term_sequence sep' prec tms =
  if tms == [] then empty
  else hcat (punctuate (text sep') (map (print_term prec) tms))

print_binder :: Int -> Term -> Doc
print_binder prec tm = case rator tm of
  Just r -> let absf = is_gabs tm in
    let s = if absf then "\\" else name_of r in
    let collectvs tm' = if absf then
                         if is_abs tm' then
                           case (dest_abs tm') of
                             Just (v,t) -> let (vs,bod) = collectvs t
                                           in ((False,v):vs,bod)
                             _ -> ([],tm')
                         else if is_gabs tm' then
                           case (dest_gabs tm') of
                             Just (v,t) -> let (vs,bod) = collectvs t
                                           in ((True,v):vs,bod)
                             _ -> ([],tm')
                         else ([],tm')
                       else if is_comb tm' then
                         case rator tm' of
                          Just r'' -> if (name_of r'') == s then
                            case rand tm' of
                              Just r' -> if is_abs r' then
                                case (dest_abs r') of
                                  Just (v,t) -> let (vs,bod) = collectvs t
                                                in ((False,v):vs,bod)
                                  _ -> ([],tm')
                                else if is_gabs r' then
                                  case (dest_gabs r') of
                                    Just (v,t) -> let (vs,bod) = collectvs t
                                                  in ((True,v):vs,bod)
                                    _ -> ([],tm')
                                else ([],tm')
                              _ -> ([],tm')
                            else ([],tm')
                          _ -> ([],tm')
                       else ([],tm') in
    let (vs,bod) = collectvs tm in
      (prec_parens prec) (hcat ([
        text s,
        (if all Char.isAlphaNum s then text " " else empty)]
        ++ (map (\ (b,x) -> hcat [
              ((if b then parens else id) (print_term 0 x)),
              text " "] )
            (init vs))
        ++ [
         (if fst (last vs) then text "(" else empty),
         print_term 0 (snd(last vs)),
         (if fst (last vs) then text ")" else empty),
         text ".",
         (if length vs == 1 then text " " else empty),
         print_term 0 bod
        ]
       ))
  _ -> empty

print_clauses :: [[Term]] -> Doc
print_clauses cls = case cls of
  [] -> empty
  c:cls' -> vcat ((print_clause c):(map (\cl -> hcat [text "| ",print_clause cl]) cls'))

print_clause :: [Term] -> Doc
print_clause cl = case cl of
  [p,g,r] -> hcat [print_term 1 p,
                   text " when ",
                   print_term 1 g,
                   text " -> ",
                   print_term 1 r]
  [p,r] -> hcat [print_term 1 p,
                 text " -> ",
                 print_term 1 r]
  _ -> empty
