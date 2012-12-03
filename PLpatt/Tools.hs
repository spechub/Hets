module PLpatt.Tools where

import PLpatt.Sign
import PLpatt.AS_BASIC_PLpatt as AS_BASIC

bool_from_pt :: parse.tree -> Form
bool_from_pt x = case x
  of parse.app(n,args) -> (if (parse.qualIDSplitSecond(n) == "bool") then (if (length(args) == 0) then prop_bool(parse.qualIDSplitFirst(n)) else error ("error: " + "bad number of arguments, expected 0")) else (if (n == "not") then (if (length(args) == 1) then not(bool_from_pt((args !! 0))) else error ("error: " + "bad number of arguments, expected 1")) else (if (n == "and") then (if (length(args) == 2) then and(bool_from_pt((args !! 0)),bool_from_pt((args !! 1))) else error ("error: " + "bad number of arguments, expected 2")) else (if (n == "or") then (if (length(args) == 2) then or(bool_from_pt((args !! 0)),bool_from_pt((args !! 1))) else error ("error: " + "bad number of arguments, expected 2")) else error ("error: " + ("illegal identifier: " + n))))))
   parse.bind(n,v,s) -> error ("error: " + ("illegal identifier: " + n))
   parse.tbind(n,a,v,s) -> error ("error: " + ("illegal identifier: " + n))
   parse.var(n) -> error ("error: " + "variables not allowed here")


decl_from_pt :: parse.decl -> Decl
decl_from_pt d = case d
  of instance(i,p,args) -> (if (p == "axiom") then (if (length(args) == 1) then axiom_decl(i,[bool_from_pt((args !! 0))]) else error ("error: " + "bad number of arguments, expected 1")) else (if (p == "prop") then (if (length(args) == 0) then prop_decl(i,[]) else error ("error: " + "bad number of arguments, expected 0")) else error ("error: " + "illegal pattern")))


sign_from_pt :: parse.sign -> Sigs
sign_from_pt sg = (map decl_from_pt sg)

axiom_from_pt :: parse.tree -> Form
axiom_from_pt ax = bool_from_pt(ax)

theo_from_pt :: parse.theo -> Theo
theo_from_pt th = theo{sign = sign_from_pt((sign th)),axioms = (map axiom_from_pt (axioms th))}

bool_to_lf :: Form -> lf.exp
bool_to_lf x = case x
  of or(x0,x1) -> lf.app(Or,[bool_to_lf(x0),bool_to_lf(x1)])
   and(x0,x1) -> lf.app(And,[bool_to_lf(x0),bool_to_lf(x1)])
   not(x0) -> lf.app(Not,[bool_to_lf(x0)])
   prop_bool(i,[]) -> lf.qapp(i,Form,[])


decl_to_lf :: Decl -> lf.decl
decl_to_lf d = case d
  of prop_decl(n,[]) -> lf.instance(Prop,n,[])
   axiom_decl(n,[x0]) -> lf.instance(Axiom,n,[bool_to_lf(x0)])


sign_to_lf :: Sigs -> lf.sign
sign_to_lf sg = (map decl_to_lf sg)

axiom_to_lf :: Form -> lf.decl
axiom_to_lf ax = lf.decl(_,bool_to_lf(ax))

theo_to_lf :: Theo -> lf.sign
theo_to_lf th = (sign_to_lf((sign th)) ++ (map axiom_to_lf (axioms th)))


