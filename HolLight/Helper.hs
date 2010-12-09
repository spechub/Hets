{- |
Module      :  $Header$
Description :  Helper functions for dealing with terms (mainly for pretty printing which is directly adapted from hollight)
Copyright   :  (c) Jonathan von Schroeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  jonathan.von_schroeder@dfki.de
Stability   :  experimental
Portability :  portable

-}

module HolLight.Helper where

import Data.Maybe (fromJust,isJust,maybe,catMaybes)
import HolLight.Term
import Data.List (union,(\\))
import Common.Doc

fromRight e = case e of
  Right t -> t
  Left _ -> error "fromRight"

is_prefix tm = case tm of
  Var _ _ (HolTermInfo (Prefix,_)) -> True
  Const _ _ (HolTermInfo (Prefix,_)) -> True
  _ -> False

pp_print_type = sot 0

soc sep flag ss = if length ss == 0 then empty
  else let s = foldr1 (\s1 s2 -> hcat[s1,text sep,s2]) ss
       in if flag then parens s else s

sot pr ty = case (dest_vartype ty,dest_type ty) of {- exactly one of these is not Nothing-}
  (Just vtype,_) -> text vtype
  (_,Just t) -> case t of
    (con,[]) -> text con
    ("fun",[ty1,ty2]) -> soc "->" (pr > 0) [sot 1 ty1,sot 0 ty2]
    ("sum",[ty1,ty2]) -> soc "+" (pr > 2) [sot 3 ty1,sot 2 ty2]
    ("prod",[ty1,ty2]) -> soc "#" (pr > 4) [sot 5 ty1,sot 4 ty2]
    ("cart",[ty1,ty2]) -> soc "^" (pr > 6) [sot 6 ty1,sot 7 ty2]
    (con,args) -> hcat [soc "," True (map (sot 0) args),text con]
  _ -> empty {- doesn't happen -}

{- lib.ml -}
rev_assocd a l d = case l of
  [] -> d
  (x,y):t -> if y == a then x
                       else rev_assocd a t d

{- fusion.ml -}
dest_var v = case v of
  Var s ty _ -> Just (s,ty)
  _ -> Nothing

is_var v = isJust (dest_var v)

frees tm = case tm of
  Var _ _ _ -> [tm]
  Const _ _ _ -> []
  Abs bv bod -> (frees bod) \\ [bv]
  Comb s t  -> union (frees s) (frees t)

vfree_in v tm = case tm of
  Abs bv bod -> v /= bv && vfree_in v bod
  Comb s t -> vfree_in v s || vfree_in v t
  _ -> tm == v

variant avoid v = if not (any (vfree_in v) avoid) then Just v
                  else case v of
                         Var s ty p -> variant avoid (Var (s++"'") ty p)
                         _ -> Nothing

vsubst =
  let vsubst' ilist tm = case tm of
                           Var _ _ _ -> Just $ rev_assocd tm ilist tm
                           Const _ _ _ -> Just tm
                           Comb s t -> case (vsubst' ilist s,vsubst ilist t) of
                             (Just s',Just t') -> if (s'==s && t'==t)
                                                  then Just tm
                                                  else Just (Comb s' t')
                             _ -> Nothing
                           Abs v s -> let ilist' = filter (\ (t,x) -> x /= v)
                                                          ilist
                             in if ilist' == [] then Just tm
                                else case vsubst ilist' s of
                                  Just s' -> if s' == s
                                    then Just tm
                                    else if any (\ (t,x) -> vfree_in v t
                                                            && vfree_in x s)
                                                ilist'
                                         then case variant [s'] v of
                                           Just v' -> case vsubst
                                                        ((v',v):ilist') s of
                                             Just t' -> Just (Abs v' t')
                                             _ -> Nothing
                                           _ -> Nothing
                                         else Just (Abs v s')
                                  _ -> Nothing
  in \ theta ->
    if theta == [] then (\ tm -> Just tm) else
    if all (\ (t,x) -> case (type_of t, dest_var x) of
                         (Just t',Just (_,x')) -> t' == x'
                         _ -> False) theta then vsubst theta
    else (\ _ -> Nothing)

dest_comb c = case c of
  Comb f x -> Just (f,x)
  _ -> Nothing

is_comb c = isJust (dest_comb c)

dest_const c = case c of
  Const s ty _ -> Just (s,ty)
  _ -> Nothing

is_const c = isJust (dest_const c)

dest_abs a = case a of
  Abs v b -> Just (v,b)
  _ -> Nothing

is_abs a = isJust (dest_abs a)

rator tm = maybe Nothing (Just . fst) (dest_comb tm)

rand tm = maybe Nothing (Just . snd) (dest_comb tm)

splitlist dest x = case dest x of
  Just (l,r) -> let (ls,res) = splitlist dest r
                in (l:ls,res)
  _ -> ([],x)

rev_splitlist dest x =
  let rsplist ls x' = case dest x' of
                       Just (l,r) -> rsplist (r:ls) l
                       _ -> (x',ls)
  in rsplist [] x

type_of tm = case tm of
  Var _ ty _ -> Just ty
  Const _ ty _ -> Just ty
  Comb s _ -> case type_of s of
                Just t -> case dest_type t of
                            Just (_,x:x1:xs) -> Just x1
                            _ -> Nothing
                _ -> Nothing
  Abs (Var _ ty _) t -> case type_of t of
                         Just t' -> Just (TyApp "fun" [ty,t'])
                         _ -> Nothing
  _ -> Nothing

dest_type a = case a of
  TyApp s ty -> Just (s,ty)
  _ -> Nothing

dest_vartype t = case t of
  TyVar s -> Just s
  _ -> Nothing

type_subst i ty = case ty of
  TyApp tycon args -> let args' = map (type_subst i) args
                      in if args' == args then ty else TyApp tycon args'
  _ -> rev_assocd ty i ty

mk_eq (l,r) = case (type_of l,mk_const ("=",[])) of
               (Just ty,Just eq) -> case inst [(ty,TyVar "A")] eq of
                                Right eq_tm -> case mk_comb (eq_tm,l) of
                                  Just m1 -> mk_comb (m1,r)
                                  _ -> Nothing
                                _ -> Nothing
               _ -> Nothing

inst =
  let inst' env tyin tm = case tm of
                            Var n ty at -> let ty' = type_subst tyin ty
                              in let tm' = if ty' == ty then tm
                                           else (Var n ty' at)
                                 in if (rev_assocd tm' env tm) == tm
                                    then Right tm'
                                    else Left tm'
                            Const c ty at -> let ty' = type_subst tyin ty
                              in if ty' == ty
                                 then Right tm
                                 else Right (Const c ty' at)
                            Comb f x -> case (inst' env tyin f,
                                              inst' env  tyin x) of
                                          (Right f',Right x') -> if f' == f
                                            && x' == x then Right tm
                                                       else Right (Comb f' x')
                                          (Left c, _) -> Left c
                                          (_,Left c) -> Left c
                            Abs y t -> case inst' [] tyin y of
                              Right y' -> let env' = (y,y'):env
                                in case inst' env' tyin t of
                                     Right t' -> if y' == y &&
                                                    t' == t
                                       then Right tm
                                       else Right (Abs y' t')
                                     Left w' -> if w' /= y'
                                       then Left w'
                                       else let ifrees = map (fromRight .
                                                               (inst' [] tyin))
                                                              (frees t) in
                                             case variant ifrees y' of
                                               Just y'' ->
                                                case (dest_var y'',dest_var y) of
                                                  (Just (v1,_),Just (_,v2)) ->
                                                    let z = (Var v1 v2 (HolTermInfo (Normal,Nothing)))
                                                    in case vsubst [(z,y)] t of
                                                         Just s -> inst' env tyin
                                                           (Abs z s)
                                                         _ -> Left w'
                                                  _ -> Left w'
                                               _ -> Left w'
                              _ -> Left tm
  in (\tyin -> if tyin == [] then (\tm -> Right tm) else inst' [] tyin)

mk_comb (f,a) = case type_of f of
  Just (TyApp "fun" [ty,_]) -> case type_of a of
    Just t -> if ty == t then Just (Comb f a) else Nothing
    _ -> Nothing
  _ -> Nothing

eq_type = TyApp "fun" [
  TyVar "A",
  TyApp "fun" [
    TyVar "A",
    TyApp "bool" []
  ]]

mk_const (name,theta) = if name == "="
                        then Just (Const name
                                   (type_subst theta eq_type)
                                   (HolTermInfo ((InfixR 12),Nothing)))
                        else Nothing

{- basics.ml -}
dest_binder s tm = case tm of
  Comb (Const s' _ _) (Abs x t) ->
    if (s'==s) then Just (x,t)
    else Nothing
  _ -> Nothing

dest_exists = dest_binder "?"

strip_exists = splitlist dest_exists

dest_forall = dest_binder "!"

strip_forall = splitlist dest_forall

strip_comb = rev_splitlist dest_comb

body tm = case dest_abs tm of
  Just (_,ret) -> Just ret
  _ -> Nothing

dest_numeral tm =
  let dest_num tm = case dest_const tm of
                      Just ("_0",_) -> Just (toInteger 0)
                      _ -> case dest_comb tm of
                             Just (l,r) -> case dest_num r of
                                             Just i ->
                                               let n = (toInteger 2) * i
                                               in case dest_const l of
                                                    Just ("BIT0",_) -> Just n
                                                    Just ("BIT1",_) -> Just (n
                                                      + (toInteger 1))
                                                    _ -> Nothing
                                             _ -> Nothing
                             _ -> Nothing
  in case dest_comb tm of
       Just (l,r) -> case dest_const l of
                     Just ("NUMERAL",_) -> dest_num r
                     _ -> Nothing
       _ -> Nothing

dest_binary' s tm = case tm of
  Comb (Comb (Const s' _ _) l) r -> if s' == s then Just (l,r)
                                  else Nothing
  _ -> Nothing

dest_cons = dest_binary' "CONS"

dest_list tm = let (tms,nil) = splitlist dest_cons tm
               in case dest_const nil of
                    Just ("NIL",_) -> Just tms
                    _ -> Nothing

dest_gabs tm =
  let dest_geq = dest_binary' "GEQ"
  in if is_abs tm then dest_abs tm
     else case dest_comb tm of
            Just (l,r) -> case dest_const l of
                            Just ("GABS",_) -> case body r of
                              Just b -> case dest_geq(snd(strip_forall b)) of
                                Just (ltm,rtm) -> case rand ltm of
                                  Just r -> Just (r,rtm)
                                  _ -> Nothing
                                _ -> Nothing
                              _ -> Nothing
                            _ -> Nothing
            _ -> Nothing

is_gabs tm = isJust (dest_gabs tm)

strip_gabs = splitlist dest_gabs

dest_fun_ty ty = case ty of
  TyApp "fun" [ty1,ty2] -> Just (ty1,ty2)
  _ -> Nothing

dest_let tm = let (l,aargs) = strip_comb tm
              in case dest_const l of
                   Just ("LET",_) ->
                     let (vars,lebod) = strip_gabs (head aargs)
                     in let eqs = zip vars (tail aargs)
                        in case dest_comb lebod of
                             Just (le,bod) -> case dest_const le of
                                                Just ("LET_END",_) -> Just (eqs,bod)
                                                _ -> Nothing
                             _ -> Nothing
                   _ -> Nothing

{- printer.ml -}
name_of tm = case tm of
  Var x ty _ -> x
  Const x ty _ -> x
  _ -> ""

{- printer.ml - pp_print_term -}
reverse_interface (s,tm) = case tm of
  Var s' _ ti -> case ti of
    HolTermInfo (_,Just (s'',pt)) -> (s'',Just pt)
    _ -> (s,Nothing)
  Const s' _ ti -> case ti of
    HolTermInfo (_,Just (s'',pt)) -> (s'',Just pt)
    _ -> (s,Nothing)
  _ -> (s,Nothing)

dest_binary c tm = case (dest_comb tm) of {- original name: DEST_BINARY -}
  Just (il,r) -> case (dest_comb il) of
    Just (i,l) -> if (i == c) ||
      (is_const i && is_const c &&
       (fst(reverse_interface((fst(fromJust(dest_const i)),i)))
       == fst(reverse_interface((fst(fromJust(dest_const c)),i)))))
      then Just (l,r)
      else Nothing
    _ -> Nothing
  _ -> Nothing

powerof10 n = (10*(div n 10)) == n

bool_of_term t = case t of
  Const "T" _ _ -> Just True
  Const "F" _ _ -> Just False
  _ -> Nothing

code_of_term t =
  let (f,tms) = strip_comb t in
  if not(is_const f && fst(fromJust(dest_const f)) == "ASCII")
     || not(length tms == 8)
  then Nothing
  else let bools = map bool_of_term (reverse tms)
       in if length (filter ((==)Nothing) bools) == 0 then
          Just (foldr (\b f -> if b then 1 + 2 * f else 2 * f)
                0 (catMaybes bools))
          else Nothing

rand_rator v = case rator v of
  Just v1 -> rand v1
  _ -> Nothing

dest_clause tm = case maybe Nothing (Just . strip_exists)
                      (maybe Nothing body (body tm)) of
  Just (_,pbod) -> let (s,args) = strip_comb pbod
                   in case (name_of s,length args) of
                     ("_UNGUARDED_PATTERN",2) ->
                       case (rand_rator (args!!0),
                             rand_rator (args!!1)) of
                         (Just _1,Just _2) -> Just [_1,_2]
                         _ -> Nothing
                     ("_GUARDED_PATTERN",3) ->
                       case (rand_rator (args!!0),
                             rand_rator (args!!2)) of
                         (Just _1, Just _3) -> Just [_1,args!!1,_3]
                         _ -> Nothing
                     _ -> Nothing
  _ -> Nothing

dest_clauses tm = let (s,args) = strip_comb tm
                  in if name_of s == "_SEQPATTERN" && length args == 2
                     then case dest_clauses (args!!1) of
                       Just cs -> case (dest_clause (args!!0)) of
                         Just c -> Just (c:cs)
                         _ -> Nothing
                       _ -> Nothing
                     else case dest_clause tm of
                       Just c -> Just [c]
                       _ -> Nothing

aright tm = case tm of
  Var _ _ (HolTermInfo ((InfixR _),_))  -> True
  Const _ _ (HolTermInfo ((InfixR _),_)) -> True
  _ -> False

get_prec tm = case tm of
  Var _ _ (HolTermInfo ((InfixR i),_))  -> i
  Const _ _ (HolTermInfo ((InfixR i),_)) -> i
  _ -> 0

parses_as_binder tm = case tm of
  Var _ _ (HolTermInfo (Binder,_))  -> True
  Const _ _ (HolTermInfo (Binder,_)) -> True
  _ -> False

can_get_infix_status tm = case tm of
  Var _ _ (HolTermInfo (InfixR _,_)) -> True
  Var _ _ (HolTermInfo (InfixL _,_)) -> True
  Const _ _ (HolTermInfo (InfixR _,_)) -> True
  Const _ _ (HolTermInfo (InfixL _,_)) -> True
  _ -> False
