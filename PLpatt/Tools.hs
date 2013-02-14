module PLpatt.Tools where

import PLpatt.Sign
import PLpatt.AS_BASIC_PLpatt as AS_BASIC
import Generic.Tools as Generic

bool_from_pt :: Generic.Tree -> Form
bool_from_pt x = case x
  of parse.app(n,args) -> (if (parse.qualIDSplitSecond(n) == "bool") then (if (length(args) == 0) then prop_bool(parse.qualIDSplitFirst(n)) else error ("error: " + "bad number of arguments, expected 0")) else error ("error: " + ("illegal identifier: " + n)))
   parse.bind(n,v,s) -> error ("error: " + ("illegal identifier: " + n))
   parse.tbind(n,a,v,s) -> error ("error: " + ("illegal identifier: " + n))
   parse.var(n) -> error ("error: " + "variables not allowed here")


decl_from_pt :: Generic.Decl -> Decl
decl_from_pt d = case d
  of Decl(i,p,args) -> (if (p == "axiom") then (if (length(args) == 1) then axiom_decl(i,[bool_from_pt((args !! 0))]) else error ("error: " + "bad number of arguments, expected 1")) else (if (p == "prop") then (if (length(args) == 0) then prop_decl(i,[]) else error ("error: " + "bad number of arguments, expected 0")) else error ("error: " + "illegal pattern")))


sign_from_pt :: Generic.Sign -> Sigs
sign_from_pt sg = (map decl_from_pt sg)

axiom_from_pt :: Generic.Tree -> Form
axiom_from_pt ax = bool_from_pt(ax)

theo_from_pt :: Generic.Theo -> Theo
theo_from_pt th = theo{sign = sign_from_pt((sign th)),axioms = (map axiom_from_pt (axioms th))}


