module PLpatt.Tools where

import PLpatt.Sign
import PLpatt.AS_BASIC_PLpatt as AS_BASIC
import MMT.Tools as Generic

bool_from_pt :: Generic.Tree -> Form
bool_from_pt x = case x
  of Generic.Application(n,args) -> (if (Generic.qualIDSplitSecond(n) == "bool") then (if (length(args) == 0) then prop_bool(Generic.qualIDSplitFirst(n)) else Nothing) else (if (n == "false") then (if (length(args) == 0) then false() else Nothing) else (if (n == "true") then (if (length(args) == 0) then true() else Nothing) else (if (n == "not") then (if (length(args) == 1) then not(bool_from_pt((args !! 0))) else Nothing) else (if (n == "and") then (if (length(args) == 2) then and(bool_from_pt((args !! 0)),bool_from_pt((args !! 1))) else Nothing) else (if (n == "or") then (if (length(args) == 2) then or(bool_from_pt((args !! 0)),bool_from_pt((args !! 1))) else Nothing) else Nothing))))))
   Generic.Bind(n,v,s) -> Nothing
   Generic.Tbind(n,a,v,s) -> Nothing
   Generic.Variable(n) -> Nothing


decl_from_pt :: Generic.Decl -> Decl
decl_from_pt d = case d
  of Decl(i,p,args) -> (if (p == "axiom") then (if (length(args) == 1) then axiom_decl(i,[bool_from_pt((args !! 0))]) else Nothing) else (if (p == "prop") then (if (length(args) == 0) then prop_decl(i,[]) else Nothing) else Nothing))


sign_from_pt :: Generic.Sign -> Sigs
sign_from_pt sg = (map decl_from_pt sg)

axiom_from_pt :: Generic.Tree -> Form
axiom_from_pt ax = bool_from_pt(ax)

theo_from_pt :: Generic.Theo -> Theo
theo_from_pt th = theo{sign = sign_from_pt((sign th)),axioms = (map axiom_from_pt (axioms th))}


