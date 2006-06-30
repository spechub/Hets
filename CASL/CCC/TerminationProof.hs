{- | 
Module      :  $Header$
Copyright   :  (c) Mingyi Liu and Till Mossakowski and Uni Bremen 2004-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  xinga@tzi.de
Stability   :  provisional
Portability :  portable

-}

module CASL.CCC.TerminationProof where

import CASL.Print_AS_Basic()                   
import CASL.AS_Basic_CASL       
import Common.AS_Annotation
import Common.Doc
import Common.DocUtils
import CASL.CCC.TermFormula
import Common.Id
import System.Cmd
import System.IO.Unsafe
import Debug.Trace


{- 
   Automatic termination proof
   using AProVE, see http://aprove.informatik.rwth-aachen.de/

   interface to AProVE system, using system
   transform CASL signature to AProVE Input Language, 
   CASL formulas to AProVE term rewrite systems
-}

terminationProof :: (PosItem f, Pretty f, Eq f) => 
                    [Named (FORMULA f)] -> Maybe Bool
terminationProof fsn 
    | null all_axioms = Just True
    | proof == "YES\n" = Just True
    | proof == "MAYBE\n" = Nothing
    | proof == "NO\n" = Just False
    | otherwise = error "termination proof"
    where
    fs1 = map sentence (filter is_user_or_sort_gen fsn)
    fs = trace (showDoc fs1 "all formulars") fs1
    all_axioms1 = filter (\f->(not $ is_Sort_gen_ax f) &&
                              (not $ is_Membership f) &&
                              (not $ is_ex_quanti f) &&
                              (not $ is_Def f)) fs
    all_axioms = trace (showDoc all_axioms1 "Terminal_allAxiom") all_axioms1
    allVar vs = everyOnce $ concat vs   
    varsStr vars str                               
        | null vars = str
        | otherwise = if null str then varsStr (tail vars) (tokStr $ head vars)
                      else varsStr (tail vars) (str ++ " " ++ 
                                                (tokStr $ head vars))
    --  transform all axioms to string
    axiomStr axs str
        | null axs = str
        | otherwise = 
            axiomStr (tail axs) (str ++ (axiom_str $ (head axs)) ++ "\n")
    impli_equiv = filter is_impli_equiv all_axioms
    n_impli_equiv = filter (not.is_impli_equiv) all_axioms
    auxAxstr afs i str
        | null afs = str
        | otherwise =
              auxAxstr (tail afs) (snd tmp) (str ++ (fst tmp))
            where tmp = impli_equiv_str i (head afs)
    axAux = auxAxstr impli_equiv 1 ""  
    axhead = "(RULES\neq(t1,t1) -> true;\n" ++ 
             "eq(t1,t2) -> false;\n" ++
             "when_else(t1,true,t2) -> t1\n" ++ 
             "when_else(t1,false,t2) -> t2\n"
    c_vars = ("(VAR " ++ (varsStr (allVar $ map varOfAxiom $ 
                                   all_axioms) "") ++ ")\n")
    c_axms = if null n_impli_equiv 
             then (axhead ++ axAux ++ ")\n")
             else (axhead ++ (axiomStr n_impli_equiv "") ++ axAux ++ ")\n")
    ipath = "/tmp/Input.trs"
    opath = "/tmp/Result.txt"
    proof = unsafePerformIO (do
                writeFile ipath (c_vars ++ c_axms)
                system ("java -jar CASL/Termination/AProVE.jar -u cli -m " ++
                        "wst -p plain " ++ 
                        ipath ++ " | head -n 1 > " ++ opath)
                res <- readFile opath
                return res)


opSymStr :: OP_SYMB -> String 
opSymStr os = case os of
                Op_name on -> idStr on
                Qual_op_name on _ _ -> idStr on


predSymStr :: PRED_SYMB -> String
predSymStr ps = case ps of 
                  Pred_name pn -> idStr pn 
                  Qual_pred_name pn _ _ -> idStr pn


{- transform Implication to string:
   i: (phi => f(t_1,...,t_m)=t)
     Example: 
                X=e => f(t_1,...,t_m)=t
     str -->   f(t_1,...,t_m) -> U(X,t_1,...,t_m)
                U(e,t_1,...t_m) -> t
   P.S. Bool ignore

   ii: (phi1  => p(t_1,...,t_m)<=>phi)
     Example:
            X=e => p(t_1,...,t_m) <=> f(tt_1,...,tt_n)=t
     str --> X=e =>  p(t_1,...,t_m)  => f(tt_1,...,tt_n)=t  --> 
                  f(tt_1,...,tt_n) -> U1(X,p(t_1,...,t_m),tt_1,...,tt_n)
                  U1(e,true,tt_1,...,tt_n) -> t
          --> X=e =>  f(tt_1,...,tt_n)=t => p(t_1,...,t_m)   --> 
                  p(t_1,...,t_m) -> U2(X,f(tt_1,...,tt_n),t_1,...,t_m)
                  U2(e,t,t_1,...,t_m) -> true 
-}
impli_str :: Int -> FORMULA f -> (String,Int)
impli_str index f =
  case (quanti f) of
    Implication (Predication predS1 ts1 _) f1 _ _ ->
        case (quanti f1) of
          Conjunction _ _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
              "))\n" ++
              fk1 ++ "(true) -> true\n"),(index+1))
          Negation (Conjunction _ _) _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
              "))\n" ++
              fk1 ++ "(true) -> false\n"),(index+1))
          Disjunction _ _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
              "))\n" ++
              fk1 ++ "(true) -> true\n"),(index+1))
          Negation (Disjunction _ _) _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
              "))\n" ++
              fk1 ++ "(true) -> false\n"),(index+1))
          Predication predS2 ts2 _ ->
              (((predSymStr predS2) ++ "(" ++ (terms_str ts2) ++ ") -> " ++
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
              ")," ++ (terms_str ts2) ++ ")\n" ++
              fk1 ++ "(true," ++ (terms_str ts2) ++ ") -> true\n" ),
              (index+1))
          Negation (Predication predS2 ts2 _) _ ->
              (((predSymStr predS2) ++ "(" ++ (terms_str ts2) ++ ") -> " ++
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
              ")," ++ (terms_str ts2) ++ ")\n" ++
              fk1 ++ "(true," ++ (terms_str ts2) ++ ") -> false\n" ),
              (index+1))
          Strong_equation t1 t2 _ ->
              (("eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
              ")," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk1 ++ "(true," ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> true\n"),(index + 1))
          Negation (Strong_equation t1 t2 _) _ ->
              (("eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
              ")," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk1 ++ "(true," ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> false\n"),(index + 1))
          Existl_equation t1 t2 _ ->
              (("eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
              ")," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk1 ++ "(true," ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> true\n"),(index + 1))
          Negation (Existl_equation t1 t2 _) _ ->
              (("eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
              ")," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk1 ++ "(true," ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> false\n"),(index + 1))
          Equivalence (Predication predS2 ts2 _) f2 _ ->
              case (quanti f2) of
                Conjunction _ _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (predSymStr predS2) ++ "(" ++ 
                    (terms_str ts2) ++"))\n" ++
                    fk1 ++ "(true,true) -> true\n"),(index+1))
                Negation (Conjunction _ _) _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (predSymStr predS2) ++ "(" ++ 
                    (terms_str ts2) ++"))\n" ++
                    fk1 ++ "(true,true) -> false\n"),(index+1))
                Disjunction _ _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (predSymStr predS2) ++ "(" ++ 
                    (terms_str ts2) ++"))\n" ++
                    fk1 ++ "(true,true) -> true\n"),(index+1))
                Negation (Disjunction _ _) _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (predSymStr predS2) ++ "(" ++ 
                    (terms_str ts2) ++"))\n" ++
                    fk1 ++ "(true,true) -> false\n"),(index+1))
                Predication predS3 ts3 _ ->
                    (((predSymStr predS3)++"("++(terms_str ts3)++") -> "++
                    fk1++"("++(predSymStr predS1)++"("++(terms_str ts1) ++ 
                    ")," ++ (predSymStr predS2) ++ "(" ++ (terms_str ts2) ++
                    ")," ++ (terms_str ts3) ++ ")\n" ++
                    fk1++"(true,true,"++(terms_str ts3)++") -> true\n"),
                    (index +1))
                Negation (Predication predS3 ts3 _) _ ->
                    (((predSymStr predS3)++"("++(terms_str ts3)++") -> "++
                    fk1++"("++(predSymStr predS1)++"("++(terms_str ts1) ++ 
                    ")," ++ (predSymStr predS2) ++ "(" ++ (terms_str ts2) ++
                    ")," ++ (terms_str ts3) ++ ")\n" ++
                    fk1++"(true,true,"++(terms_str ts3)++") -> false\n"),
                    (index + 1))
                Strong_equation t1 t2 _ ->
                    (("eq("++(term_str t1)++","++(term_str t2)++") -> " ++
                    fk1++"("++(predSymStr predS1)++"("++(terms_str ts1)++
                    ")," ++ (predSymStr predS2) ++ "(" ++ (terms_str ts2) ++
                    "),"++(term_str t1)++","++(term_str t2)++")\n" ++
                    fk1++"(true,true,"++(term_str t1)++","++(term_str t2)++ 
                    ") -> true\n"),(index +1))
                Negation (Strong_equation t1 t2 _) _ ->
                    (("eq("++(term_str t1)++","++(term_str t2)++") -> " ++
                    fk1++"("++(predSymStr predS1)++"("++(terms_str ts1)++
                    ")," ++ (predSymStr predS2) ++ "(" ++ (terms_str ts2) ++
                    "),"++(term_str t1)++","++(term_str t2)++")\n" ++
                    fk1++"(true,true,"++(term_str t1)++","++(term_str t2)++ 
                    ") -> false\n"),(index +1))
                Existl_equation t1 t2 _ ->
                    (("eq("++(term_str t1)++","++(term_str t2)++") -> " ++
                    fk1++"("++(predSymStr predS1)++"("++(terms_str ts1)++
                    ")," ++ (predSymStr predS2) ++ "(" ++ (terms_str ts2) ++
                    "),"++(term_str t1)++","++(term_str t2)++")\n" ++
                    fk1++"(true,true,"++(term_str t1)++","++(term_str t2)++ 
                    ") -> true\n"),(index +1))
                Negation (Existl_equation t1 t2 _) _ ->
                    (("eq("++(term_str t1)++","++(term_str t2)++") -> " ++
                    fk1++"("++(predSymStr predS1)++"("++(terms_str ts1)++
                    ")," ++ (predSymStr predS2) ++ "(" ++ (terms_str ts2) ++
                    "),"++(term_str t1)++","++(term_str t2)++")\n" ++
                    fk1++"(true,true,"++(term_str t1)++","++(term_str t2)++ 
                    ") -> false\n"),(index +1))
                _ -> error "CASL.CCC.TerminationProof.<impli_str_p_eq_p>"
          Equivalence (Strong_equation t1 t2 _) f2 _ ->
              case (quanti f2) of
                Conjunction _ _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ ")\n" ++
                    fk1 ++ "(true," ++ (term_str t2) ++ ") -> true\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++
                    ") -> " ++ fk2 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (axiom_substr (quanti f2)) ++
                    "," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
                    fk2 ++ "(true,true," ++ (term_str t1) ++ "," ++ 
                    (term_str t2) ++ ") -> true\n"),(index+2))
                Negation (Conjunction _ _) _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ ")\n" ++
                    fk1 ++ "(true," ++ (term_str t2) ++ ") -> false\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++
                    ") -> " ++ fk2 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (axiom_substr (quanti f2)) ++
                    "," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
                    fk2 ++ "(true,false," ++ (term_str t1) ++ "," ++ 
                    (term_str t2) ++ ") -> true\n"),(index+2))
                Disjunction _ _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ ")\n" ++
                    fk1 ++ "(true," ++ (term_str t2) ++ ") -> true\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++
                    ") -> " ++ fk2 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (axiom_substr (quanti f2)) ++
                    "," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
                    fk2 ++ "(true,true," ++ (term_str t1) ++ "," ++ 
                    (term_str t2) ++ ") -> true\n"),(index+2))
                Negation (Disjunction _ _) _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ ")\n" ++
                    fk1 ++ "(true," ++ (term_str t2) ++ ") -> false\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++
                    ") -> " ++ fk2 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (axiom_substr (quanti f2)) ++
                    "," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
                    fk2 ++ "(true,false," ++ (term_str t1) ++ "," ++ 
                    (term_str t2) ++ ") -> true\n"),(index+2))
                Predication predS2 ts2 _ ->
                    (((predSymStr predS2) ++ "(" ++ (terms_str ts2) ++ 
                    ") ->" ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ "," ++
                    (terms_str ts2) ++ ")\n" ++
                    fk1 ++ "(true," ++ (term_str t2) ++ "," ++ 
                    (terms_str ts2) ++ ") -> true\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++
                    ") -> " ++ fk2 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (predSymStr predS2) ++ "(" ++
                    (terms_str ts2) ++ ")," ++ (term_str t1) ++ "," ++
                    (term_str t2) ++ ")\n" ++
                    fk2 ++ "(true,true," ++ (term_str t1) ++ "," ++
                    (term_str t2) ++ ") -> true\n"),(index+2))
                Negation (Predication predS2 ts2 _) _ ->
                    (((predSymStr predS2) ++ "(" ++ (terms_str ts2) ++ 
                    ") ->" ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ "," ++
                    (terms_str ts2) ++ ")\n" ++
                    fk1 ++ "(true," ++ (term_str t2) ++ "," ++ 
                    (terms_str ts2) ++ ") -> false\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++
                    ") -> " ++ fk2 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (predSymStr predS2) ++ "(" ++
                    (terms_str ts2) ++ ")," ++ (term_str t1) ++ "," ++
                    (term_str t2) ++ ")\n" ++
                    fk2 ++ "(true,false," ++ (term_str t1) ++ "," ++
                    (term_str t2) ++ ") -> true\n"),(index+2))
                Strong_equation t3 t4 _ ->
                    (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ "," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk1 ++ "(true," ++ (term_str t2) ++ "," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t3) ++ "," ++
                    (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
                    fk1 ++ "(true," ++ (term_str t4) ++ "," ++ 
                    (term_str t1) ++ "," ++ (term_str t2) ++ ") -> true\n"),
                    (index+2))
                Negation (Strong_equation t3 t4 _) _ ->
                    (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ "," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk1 ++ "(true," ++ (term_str t2) ++ "," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> false\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ "eq(" ++ (term_str t3) ++ 
                    "," ++ (term_str t4) ++ ")" ++ (term_str t1) ++ "," ++ 
                    (term_str t2) ++ ")\n" ++
                    fk1 ++ "(true,false," ++ 
                    (term_str t1) ++ "," ++ (term_str t2) ++ ") -> true\n"),
                    (index+2))
                Existl_equation t3 t4 _ ->
                    (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ "," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk1 ++ "(true," ++ (term_str t2) ++ "," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t3) ++ "," ++
                    (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
                    fk1 ++ "(true," ++ (term_str t4) ++ "," ++ 
                    (term_str t1) ++ "," ++ (term_str t2) ++ ") -> true\n"),
                    (index+2))
                Negation (Existl_equation t3 t4 _) _ ->
                    (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ "," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk1 ++ "(true," ++ (term_str t2) ++ "," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> false\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ "eq(" ++ (term_str t3) ++ 
                    "," ++ (term_str t4) ++ ")" ++ (term_str t1) ++ "," ++ 
                    (term_str t2) ++ ")\n" ++
                    fk1 ++ "(true,false," ++ 
                    (term_str t1) ++ "," ++ (term_str t2) ++ ") -> true\n"),
                    (index+2))
                _ -> error "CASL.CCC.TerminationProof.<impli_str_p_eq_str>"
          Equivalence (Existl_equation t1 t2 _) f2 _ ->
              case (quanti f2) of
                Conjunction _ _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ ")\n" ++
                    fk1 ++ "(true," ++ (term_str t2) ++ ") -> true\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++
                    ") -> " ++ fk2 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (axiom_substr (quanti f2)) ++
                    "," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
                    fk2 ++ "(true,true," ++ (term_str t1) ++ "," ++ 
                    (term_str t2) ++ ") -> true\n"),(index+2))
                Negation (Conjunction _ _) _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ ")\n" ++
                    fk1 ++ "(true," ++ (term_str t2) ++ ") -> false\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++
                    ") -> " ++ fk2 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (axiom_substr (quanti f2)) ++
                    "," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
                    fk2 ++ "(true,false," ++ (term_str t1) ++ "," ++ 
                    (term_str t2) ++ ") -> true\n"),(index+2))
                Disjunction _ _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ ")\n" ++
                    fk1 ++ "(true," ++ (term_str t2) ++ ") -> true\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++
                    ") -> " ++ fk2 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (axiom_substr (quanti f2)) ++
                    "," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
                    fk2 ++ "(true,true," ++ (term_str t1) ++ "," ++ 
                    (term_str t2) ++ ") -> true\n"),(index+2))
                Negation (Disjunction _ _) _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ ")\n" ++
                    fk1 ++ "(true," ++ (term_str t2) ++ ") -> false\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++
                    ") -> " ++ fk2 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (axiom_substr (quanti f2)) ++
                    "," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
                    fk2 ++ "(true,false," ++ (term_str t1) ++ "," ++ 
                    (term_str t2) ++ ") -> true\n"),(index+2))
                Predication predS2 ts2 _ ->
                    (((predSymStr predS2) ++ "(" ++ (terms_str ts2) ++ 
                    ") ->" ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ "," ++
                    (terms_str ts2) ++ ")\n" ++
                    fk1 ++ "(true," ++ (term_str t2) ++ "," ++ 
                    (terms_str ts2) ++ ") -> true\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++
                    ") -> " ++ fk2 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (predSymStr predS2) ++ "(" ++
                    (terms_str ts2) ++ ")," ++ (term_str t1) ++ "," ++
                    (term_str t2) ++ ")\n" ++
                    fk2 ++ "(true,true," ++ (term_str t1) ++ "," ++
                    (term_str t2) ++ ") -> true\n"),(index+2))
                Negation (Predication predS2 ts2 _) _ ->
                    (((predSymStr predS2) ++ "(" ++ (terms_str ts2) ++ 
                    ") ->" ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ "," ++
                    (terms_str ts2) ++ ")\n" ++
                    fk1 ++ "(true," ++ (term_str t2) ++ "," ++ 
                    (terms_str ts2) ++ ") -> false\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++
                    ") -> " ++ fk2 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (predSymStr predS2) ++ "(" ++
                    (terms_str ts2) ++ ")," ++ (term_str t1) ++ "," ++
                    (term_str t2) ++ ")\n" ++
                    fk2 ++ "(true,false," ++ (term_str t1) ++ "," ++
                    (term_str t2) ++ ") -> true\n"),(index+2))
                Strong_equation t3 t4 _ ->
                    (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ "," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk1 ++ "(true," ++ (term_str t2) ++ "," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t3) ++ "," ++
                    (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
                    fk1 ++ "(true," ++ (term_str t4) ++ "," ++ 
                    (term_str t1) ++ "," ++ (term_str t2) ++ ") -> true\n"),
                    (index+2))
                Negation (Strong_equation t3 t4 _) _ ->
                    (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ "," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk1 ++ "(true," ++ (term_str t2) ++ "," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> false\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ "eq(" ++ (term_str t3) ++ 
                    "," ++ (term_str t4) ++ ")" ++ (term_str t1) ++ "," ++ 
                    (term_str t2) ++ ")\n" ++
                    fk1 ++ "(true,false," ++ 
                    (term_str t1) ++ "," ++ (term_str t2) ++ ") -> true\n"),
                    (index+2))
                Existl_equation t3 t4 _ ->
                    (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ "," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk1 ++ "(true," ++ (term_str t2) ++ "," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t3) ++ "," ++
                    (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
                    fk1 ++ "(true," ++ (term_str t4) ++ "," ++ 
                    (term_str t1) ++ "," ++ (term_str t2) ++ ") -> true\n"),
                    (index+2))
                Negation (Existl_equation t3 t4 _) _ ->
                    (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ "," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk1 ++ "(true," ++ (term_str t2) ++ "," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> false\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ "eq(" ++ (term_str t3) ++ 
                    "," ++ (term_str t4) ++ ")" ++ (term_str t1) ++ "," ++ 
                    (term_str t2) ++ ")\n" ++
                    fk1 ++ "(true,false," ++ 
                    (term_str t1) ++ "," ++ (term_str t2) ++ ") -> true\n"),
                    (index+2))
                _ -> error "CASL.CCC.TerminationProof.<impli_str_p_eq_ex>"
          _ -> error "CASL.CCC.TerminationProof.<impli_str_p>"
    Implication (Strong_equation t1 t2 _) f1 _ _ ->
        case (quanti f1) of
          Conjunction _ _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_str t1) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ") -> true\n"),(index+1))
          Negation (Conjunction _ _) _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_str t1) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ") -> false\n"),(index+1))
          Disjunction _ _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_str t1) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ") -> true\n"),(index+1))
          Negation (Disjunction _ _) _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_str t1) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ") -> false\n"),(index+1))
          Predication predS ts _ ->
              (((predSymStr predS)++"("++(terms_str ts) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1) ++ "," ++ (terms_str ts) ++ 
              ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ "," ++ (terms_str ts) ++
              ") -> true\n"),(index+1))
          Negation (Predication predS ts _) _ ->
              (((predSymStr predS)++"("++(terms_str ts) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1) ++ "," ++ (terms_str ts) ++ 
              ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ "," ++ (terms_str ts) ++
              ") -> false\n"),(index+1))
          Strong_equation t3 t4 _ ->
              (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++ "," ++ 
              (term_str t4) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t3) ++ "," ++
              (term_str t4) ++ ") -> true\n"),(index + 1))
          Negation (Strong_equation t3 t4 _) _ ->
              (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++ "," ++ 
              (term_str t4) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t3) ++ "," ++
              (term_str t4) ++ ") -> false\n"),(index + 1))
          Existl_equation t3 t4 _ ->
              (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++ "," ++ 
              (term_str t4) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t3) ++ "," ++
              (term_str t4) ++ ") -> true\n"),(index + 1))
          Negation (Existl_equation t3 t4 _) _ ->
              (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++ "," ++ 
              (term_str t4) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t3) ++ "," ++
              (term_str t4) ++ ") -> false\n"),(index + 1))
          Equivalence (Predication predS1 ts1 _) f2 _->
              case (quanti f2) of
                Conjunction _ _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ "))\n"++
                    fk1 ++ "(" ++ (term_str t2) ++ ",true) -> true\n"),
                    (index+1))
                Negation (Conjunction _ _) _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ "))\n"++
                    fk1 ++ "(" ++ (term_str t2) ++ ",true) -> false\n"),
                    (index+1))
                Disjunction _ _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ "))\n"++
                    fk1 ++ "(" ++ (term_str t2) ++ ",true) -> true\n"),
                    (index+1))
                Negation (Disjunction _ _) _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ "))\n"++
                    fk1 ++ "(" ++ (term_str t2) ++ ",true) -> false\n"),
                    (index+1))
                Predication predS2 ts2 _ ->
                    (((predSymStr predS2)++"("++(terms_str ts2) ++ ") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ ")," ++
                    (terms_str ts2) ++ ")\n" ++
                    fk1++"("++(term_str t2)++ ",true," ++ (terms_str ts2) ++
                    ") -> true\n"),(index + 1))
                Negation (Predication predS2 ts2 _) _ ->
                    (((predSymStr predS2)++"("++(terms_str ts2) ++ ") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ ")," ++
                    (terms_str ts2) ++ ")\n" ++
                    fk1++"("++(term_str t2)++ ",true," ++ (terms_str ts2) ++
                    ") -> false\n"),(index + 1))
                Strong_equation t3 t4 _ ->
                    (("eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
                    ")," ++ (term_str t3)++","++(term_str t4) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ ",true," ++ 
                    (term_str t3)++ "," ++ (term_str t4) ++ ") -> " ++
                    "true\n"),(index + 1))
                Negation (Strong_equation t3 t4 _) _ ->
                    (("eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
                    ")," ++ (term_str t3)++","++(term_str t4) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ ",true," ++ 
                    (term_str t3)++ "," ++ (term_str t4) ++ ") -> " ++
                    "false\n"),(index + 1))
                Existl_equation t3 t4 _ ->
                    (("eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
                    ")," ++ (term_str t3)++","++(term_str t4) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ ",true," ++ 
                    (term_str t3)++ "," ++ (term_str t4) ++ ") -> " ++
                    "true\n"),(index + 1))
                Negation (Existl_equation t3 t4 _) _ ->
                    (("eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
                    ")," ++ (term_str t3)++","++(term_str t4) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ ",true," ++ 
                    (term_str t3)++ "," ++ (term_str t4) ++ ") -> " ++
                    "false\n"),(index + 1))
                _ -> error "CASL.CCC.TerminationProof.<impli_str_str_eq_p>"
          Equivalence (Strong_equation t3 t4 _) f2 _->
              case (quanti f2) of
                Conjunction _ _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (term_str t3) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ 
                    (term_str t4) ++ ") -> true\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++
                    (axiom_substr (quanti f2)) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",true," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> true\n"),
                    (index+2))
                Negation (Conjunction _ _) _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (term_str t3) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ 
                    (term_str t4) ++ ") -> false\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++
                    (axiom_substr (quanti f2)) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",false," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> true\n"),
                    (index+2))
                Disjunction _ _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (term_str t3) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ 
                    (term_str t4) ++ ") -> true\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++
                    (axiom_substr (quanti f2)) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",true," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> true\n"),
                    (index+2))
                Negation (Disjunction _ _) _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (term_str t3) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ 
                    (term_str t4) ++ ") -> false\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++
                    (axiom_substr (quanti f2)) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",false," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> true\n"),
                    (index+2))
                Predication predS ts _ ->
                    (((predSymStr predS)++"("++(terms_str ts) ++ ") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++ 
                    "," ++ (terms_str ts) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (terms_str ts) ++ ") -> true\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (predSymStr predS) ++ "(" ++ (terms_str ts) ++ ")," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",true," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> true\n"),
                    (index + 2))
                Negation (Predication predS ts _) _ ->
                    (((predSymStr predS)++"("++(terms_str ts) ++ ") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++ 
                    "," ++ (terms_str ts) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (terms_str ts) ++ ") -> false\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (predSymStr predS) ++ "(" ++ (terms_str ts) ++ ")," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",false," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> true\n"),
                    (index + 2))
                Strong_equation t5 t6 _ ->
                    (("eq("++(term_str t5)++","++(term_str t6)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> true\n" ++
                    "eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t5) ++
                    "," ++ (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t6) ++
                    "," ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true\n"),(index + 2))
                Negation (Strong_equation t5 t6 _) _ ->
                    (("eq("++(term_str t5)++","++(term_str t6)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> false\n" ++
                    "eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ ",eq(" ++ (term_str t5) ++
                    "," ++ (term_str t6) ++ ")," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",false," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true\n"),(index + 2))
                Existl_equation t5 t6 _ ->
                    (("eq("++(term_str t5)++","++(term_str t6)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> true\n" ++
                    "eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t5) ++
                    "," ++ (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t6) ++
                    "," ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true\n"),(index + 2))
                Negation (Existl_equation t5 t6 _) _ ->
                    (("eq("++(term_str t5)++","++(term_str t6)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> false\n" ++
                    "eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ ",eq(" ++ (term_str t5) ++
                    "," ++ (term_str t6) ++ ")," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",false," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true\n"),(index + 2))
                _ -> error "CASL.CCC.TerminationProof.<impli_str_str_eq_str>"
          Equivalence (Existl_equation t3 t4 _) f2 _->
              case (quanti f2) of
                Conjunction _ _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (term_str t3) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ 
                    (term_str t4) ++ ") -> true\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++
                    (axiom_substr (quanti f2)) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",true," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> true\n"),
                    (index+2))
                Negation (Conjunction _ _) _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (term_str t3) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ 
                    (term_str t4) ++ ") -> false\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++
                    (axiom_substr (quanti f2)) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",false," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> true\n"),
                    (index+2))
                Disjunction _ _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (term_str t3) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ 
                    (term_str t4) ++ ") -> true\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++
                    (axiom_substr (quanti f2)) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",true," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> true\n"),
                    (index+2))
                Negation (Disjunction _ _) _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (term_str t3) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ 
                    (term_str t4) ++ ") -> false\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++
                    (axiom_substr (quanti f2)) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",false," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> true\n"),
                    (index+2))
                Predication predS ts _ ->
                    (((predSymStr predS)++"("++(terms_str ts) ++ ") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++ 
                    "," ++ (terms_str ts) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (terms_str ts) ++ ") -> true\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (predSymStr predS) ++ "(" ++ (terms_str ts) ++ ")," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",true," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> true\n"),
                    (index + 2))
                Negation (Predication predS ts _) _ ->
                    (((predSymStr predS)++"("++(terms_str ts) ++ ") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++ 
                    "," ++ (terms_str ts) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (terms_str ts) ++ ") -> false\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (predSymStr predS) ++ "(" ++ (terms_str ts) ++ ")," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",false," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> true\n"),
                    (index + 2))
                Strong_equation t5 t6 _ ->
                    (("eq("++(term_str t5)++","++(term_str t6)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> true\n" ++
                    "eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t5) ++
                    "," ++ (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t6) ++
                    "," ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true\n"),(index + 2))
                Negation (Strong_equation t5 t6 _) _ ->
                    (("eq("++(term_str t5)++","++(term_str t6)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> false\n" ++
                    "eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ ",eq(" ++ (term_str t5) ++
                    "," ++ (term_str t6) ++ ")," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",false," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true\n"),(index + 2))
                Existl_equation t5 t6 _ ->
                    (("eq("++(term_str t5)++","++(term_str t6)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> true\n" ++
                    "eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t5) ++
                    "," ++ (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t6) ++
                    "," ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true\n"),(index + 2))
                Negation (Existl_equation t5 t6 _) _ ->
                    (("eq("++(term_str t5)++","++(term_str t6)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> false\n" ++
                    "eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ ",eq(" ++ (term_str t5) ++
                    "," ++ (term_str t6) ++ ")," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",false," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true\n"),(index + 2))
                _ -> error "CASL.CCC.TerminationProof.<impli_str_str_eq_ex>"
          _ -> error "CASL.CCC.TerminationProof.<impli_str_str>"
    Implication (Existl_equation t1 t2 _) f1 _ _ ->
        case (quanti f1) of
          Conjunction _ _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_str t1) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ") -> true\n"),(index+1))
          Negation (Conjunction _ _) _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_str t1) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ") -> false\n"),(index+1))
          Disjunction _ _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_str t1) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ") -> true\n"),(index+1))
          Negation (Disjunction _ _) _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_str t1) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ") -> false\n"),(index+1))
          Predication predS ts _ ->
              (((predSymStr predS)++"("++(terms_str ts) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1) ++ "," ++ (terms_str ts) ++ 
              ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ "," ++ (terms_str ts) ++
              ") -> true\n"),(index+1))
          Negation (Predication predS ts _) _ ->
              (((predSymStr predS)++"("++(terms_str ts) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1) ++ "," ++ (terms_str ts) ++ 
              ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ "," ++ (terms_str ts) ++
              ") -> false\n"),(index+1))
          Strong_equation t3 t4 _ ->
              (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++ "," ++ 
              (term_str t4) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t3) ++ "," ++
              (term_str t4) ++ ") -> true\n"),(index + 1))
          Negation (Strong_equation t3 t4 _) _ ->
              (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++ "," ++ 
              (term_str t4) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t3) ++ "," ++
              (term_str t4) ++ ") -> false\n"),(index + 1))
          Existl_equation t3 t4 _ ->
              (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++ "," ++ 
              (term_str t4) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t3) ++ "," ++
              (term_str t4) ++ ") -> true\n"),(index + 1))
          Negation (Existl_equation t3 t4 _) _ ->
              (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++ "," ++ 
              (term_str t4) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t3) ++ "," ++
              (term_str t4) ++ ") -> false\n"),(index + 1))
          Equivalence (Predication predS1 ts1 _) f2 _->
              case (quanti f2) of
                Conjunction _ _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ "))\n"++
                    fk1 ++ "(" ++ (term_str t2) ++ ",true) -> true\n"),
                    (index+1))
                Negation (Conjunction _ _) _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ "))\n"++
                    fk1 ++ "(" ++ (term_str t2) ++ ",true) -> false\n"),
                    (index+1))
                Disjunction _ _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ "))\n"++
                    fk1 ++ "(" ++ (term_str t2) ++ ",true) -> true\n"),
                    (index+1))
                Negation (Disjunction _ _) _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ "))\n"++
                    fk1 ++ "(" ++ (term_str t2) ++ ",true) -> false\n"),
                    (index+1))
                Predication predS2 ts2 _ ->
                    (((predSymStr predS2)++"("++(terms_str ts2) ++ ") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ ")," ++
                    (terms_str ts2) ++ ")\n" ++
                    fk1++"("++(term_str t2)++ ",true," ++ (terms_str ts2) ++
                    ") -> true\n"),(index + 1))
                Negation (Predication predS2 ts2 _) _ ->
                    (((predSymStr predS2)++"("++(terms_str ts2) ++ ") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ ")," ++
                    (terms_str ts2) ++ ")\n" ++
                    fk1++"("++(term_str t2)++ ",true," ++ (terms_str ts2) ++
                    ") -> false\n"),(index + 1))
                Strong_equation t3 t4 _ ->
                    (("eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
                    ")," ++ (term_str t3)++","++(term_str t4) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ ",true," ++ 
                    (term_str t3)++ "," ++ (term_str t4) ++ ") -> " ++
                    "true\n"),(index + 1))
                Negation (Strong_equation t3 t4 _) _ ->
                    (("eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
                    ")," ++ (term_str t3)++","++(term_str t4) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ ",true," ++ 
                    (term_str t3)++ "," ++ (term_str t4) ++ ") -> " ++
                    "false\n"),(index + 1))
                Existl_equation t3 t4 _ ->
                    (("eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
                    ")," ++ (term_str t3)++","++(term_str t4) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ ",true," ++ 
                    (term_str t3)++ "," ++ (term_str t4) ++ ") -> " ++
                    "true\n"),(index + 1))
                Negation (Existl_equation t3 t4 _) _ ->
                    (("eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
                    ")," ++ (term_str t3)++","++(term_str t4) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ ",true," ++ 
                    (term_str t3)++ "," ++ (term_str t4) ++ ") -> " ++
                    "false\n"),(index + 1))
                _ -> error "CASL.CCC.TerminationProof.<impli_str_ex_eq_p>"
          Equivalence (Strong_equation t3 t4 _) f2 _->
              case (quanti f2) of
                Conjunction _ _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (term_str t3) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ 
                    (term_str t4) ++ ") -> true\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++
                    (axiom_substr (quanti f2)) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",true," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> true\n"),
                    (index+2))
                Negation (Conjunction _ _) _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (term_str t3) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ 
                    (term_str t4) ++ ") -> false\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++
                    (axiom_substr (quanti f2)) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",false," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> true\n"),
                    (index+2))
                Disjunction _ _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (term_str t3) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ 
                    (term_str t4) ++ ") -> true\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++
                    (axiom_substr (quanti f2)) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",true," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> true\n"),
                    (index+2))
                Negation (Disjunction _ _) _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (term_str t3) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ 
                    (term_str t4) ++ ") -> false\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++
                    (axiom_substr (quanti f2)) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",false," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> true\n"),
                    (index+2))
                Predication predS ts _ ->
                    (((predSymStr predS)++"("++(terms_str ts) ++ ") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++ 
                    "," ++ (terms_str ts) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (terms_str ts) ++ ") -> true\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (predSymStr predS) ++ "(" ++ (terms_str ts) ++ ")," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",true," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> true\n"),
                    (index + 2))
                Negation (Predication predS ts _) _ ->
                    (((predSymStr predS)++"("++(terms_str ts) ++ ") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++ 
                    "," ++ (terms_str ts) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (terms_str ts) ++ ") -> false\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (predSymStr predS) ++ "(" ++ (terms_str ts) ++ ")," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",false," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> true\n"),
                    (index + 2))
                Strong_equation t5 t6 _ ->
                    (("eq("++(term_str t5)++","++(term_str t6)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> true\n" ++
                    "eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t5) ++
                    "," ++ (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t6) ++
                    "," ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true\n"),(index + 2))
                Negation (Strong_equation t5 t6 _) _ ->
                    (("eq("++(term_str t5)++","++(term_str t6)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> false\n" ++
                    "eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ ",eq(" ++ (term_str t5) ++
                    "," ++ (term_str t6) ++ ")," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",false," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true\n"),(index + 2))
                Existl_equation t5 t6 _ ->
                    (("eq("++(term_str t5)++","++(term_str t6)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> true\n" ++
                    "eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t5) ++
                    "," ++ (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t6) ++
                    "," ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true\n"),(index + 2))
                Negation (Existl_equation t5 t6 _) _ ->
                    (("eq("++(term_str t5)++","++(term_str t6)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> false\n" ++
                    "eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ ",eq(" ++ (term_str t5) ++
                    "," ++ (term_str t6) ++ ")," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",false," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true\n"),(index + 2))
                _ -> error "CASL.CCC.TerminationProof.<impli_str_ex_eq_str>"
          Equivalence (Existl_equation t3 t4 _) f2 _->
              case (quanti f2) of
                Conjunction _ _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (term_str t3) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ 
                    (term_str t4) ++ ") -> true\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++
                    (axiom_substr (quanti f2)) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",true," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> true\n"),
                    (index+2))
                Negation (Conjunction _ _) _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (term_str t3) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ 
                    (term_str t4) ++ ") -> false\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++
                    (axiom_substr (quanti f2)) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",false," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> true\n"),
                    (index+2))
                Disjunction _ _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (term_str t3) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ 
                    (term_str t4) ++ ") -> true\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++
                    (axiom_substr (quanti f2)) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",true," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> true\n"),
                    (index+2))
                Negation (Disjunction _ _) _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (term_str t3) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ 
                    (term_str t4) ++ ") -> false\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++
                    (axiom_substr (quanti f2)) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",false," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> true\n"),
                    (index+2))
                Predication predS ts _ ->
                    (((predSymStr predS)++"("++(terms_str ts) ++ ") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++ 
                    "," ++ (terms_str ts) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (terms_str ts) ++ ") -> true\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (predSymStr predS) ++ "(" ++ (terms_str ts) ++ ")," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",true," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> true\n"),
                    (index + 2))
                Negation (Predication predS ts _) _ ->
                    (((predSymStr predS)++"("++(terms_str ts) ++ ") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++ 
                    "," ++ (terms_str ts) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (terms_str ts) ++ ") -> false\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (predSymStr predS) ++ "(" ++ (terms_str ts) ++ ")," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",false," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> true\n"),
                    (index + 2))
                Strong_equation t5 t6 _ ->
                    (("eq("++(term_str t5)++","++(term_str t6)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> true\n" ++
                    "eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t5) ++
                    "," ++ (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t6) ++
                    "," ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true\n"),(index + 2))
                Negation (Strong_equation t5 t6 _) _ ->
                    (("eq("++(term_str t5)++","++(term_str t6)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> false\n" ++
                    "eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ ",eq(" ++ (term_str t5) ++
                    "," ++ (term_str t6) ++ ")," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",false," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true\n"),(index + 2))
                Existl_equation t5 t6 _ ->
                    (("eq("++(term_str t5)++","++(term_str t6)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> true\n" ++
                    "eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t5) ++
                    "," ++ (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t6) ++
                    "," ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true\n"),(index + 2))
                Negation (Existl_equation t5 t6 _) _ ->
                    (("eq("++(term_str t5)++","++(term_str t6)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> false\n" ++
                    "eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ ",eq(" ++ (term_str t5) ++
                    "," ++ (term_str t6) ++ ")," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",false," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true\n"),(index + 2))
                _ -> error "CASL.CCC.TerminationProof.<impli_str_ex_eq_ex>"
          _ -> error "CASL.CCC.TerminationProof.<impli_str_ex>"
    _ -> error "CASL.CCC.TerminationProof.<impli_str>"
  where fk1 = "af" ++ (show index)
        fk2 = "af" ++ (show $ index +1)


{- transform Equivalence to str: 
   (p(t_1,...,t_m) <=> phi)
     Example:
             p(t_1,...,t_m) <=> f(tt_1,...,tt_n)=t
     str --> p(t_1,...,t_m)  => f(tt_1,...,tt_n)=t --> 
                 f(tt_1,...,tt_n) -> U1(p(t_1,...,t_m),tt_1,...,tt_n)
                 U1(true,tt_1,...,tt_n) -> t
          --> f(tt_1,...,tt_n)=t => p(t_1,...,t_m)  --> 
                 p(t_1,...,t_m) -> U2(f(tt_1,...,tt_n),t_1,...,t_m)
                 U2(t,t_1,...t_m) -> true 
-}
equiv_str :: Int -> FORMULA f -> (String,Int)
equiv_str index f =
  case (quanti f) of
    Equivalence (Predication predS1 ts1 _) f1 _ ->
        case (quanti f1) of
          Conjunction _ _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
              "))\n" ++
              fk1 ++ "(true) -> true\n"),(index+1))
          Negation (Conjunction _ _) _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
              "))\n" ++
              fk1 ++ "(true) -> false\n"),(index+1))
          Disjunction _ _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
              "))\n" ++
              fk1 ++ "(true) -> true\n"),(index+1))
          Negation (Disjunction _ _) _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
              "))\n" ++
              fk1 ++ "(true) -> false\n"),(index+1))              
          Predication predS2 ts2 _ ->
              (((predSymStr predS2) ++ "(" ++ (terms_str ts2) ++ ") -> " ++
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
              ")," ++ (terms_str ts2) ++ ")\n" ++
              fk1 ++ "(true," ++ (terms_str ts2) ++ ") -> true\n"),
              (index +1))
          Negation (Predication predS2 ts2 _) _ ->           -- !!
              (((predSymStr predS2) ++ "(" ++ (terms_str ts2) ++ ") -> " ++
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
              ")," ++ (terms_str ts2) ++ ")\n" ++
              fk1 ++ "(true," ++ (terms_str ts2) ++ ") -> false\n"),
              (index +1))
          Strong_equation t1 t2 _ -> 
              (("eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
              ")," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk1++"(true,"++(term_str t1)++","++(term_str t2)++") -> " ++
              "true\n"),(index + 1))
          Negation (Strong_equation t1 t2 _) _ ->
              (("eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
              ")," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk1 ++ "(true," ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> false\n"),(index +1))
          Existl_equation t1 t2 _ -> 
              (("eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
              ")," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk1++"(true,"++(term_str t1)++","++(term_str t2)++") -> " ++
              "true\n"),(index + 1))
          Negation (Existl_equation t1 t2 _) _ ->
              (("eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
              ")," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk1 ++ "(true," ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> false\n"),(index +1))
          _ -> error "CASL.CCC.TerminationProof.<equiv_str_pred>"
    Equivalence (Strong_equation t1 t2 _) f1 _ ->
        case (quanti f1) of
          Conjunction _ _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_str t1) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ") -> true\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk2 ++ "(" ++ (axiom_substr (quanti f1)) ++ "," ++
              (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk2 ++ "(true," ++ (term_str t1) ++ "," ++
              (term_str t2) ++ ") -> true\n"),(index+2))
          Negation (Conjunction _ _) _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_str t1) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ") -> false\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk2 ++ "(" ++ (axiom_substr (quanti f1)) ++ "," ++
              (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk2 ++ "(false," ++ (term_str t1) ++ "," ++
              (term_str t2) ++ ") -> true\n"),(index+2))
          Disjunction _ _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_str t1) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ") -> true\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk2 ++ "(" ++ (axiom_substr (quanti f1)) ++ "," ++
              (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk2 ++ "(true," ++ (term_str t1) ++ "," ++
              (term_str t2) ++ ") -> true\n"),(index+2))
          Negation (Disjunction _ _) _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_str t1) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ") -> false\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk2 ++ "(" ++ (axiom_substr (quanti f1)) ++ "," ++
              (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk2 ++ "(false," ++ (term_str t1) ++ "," ++
              (term_str t2) ++ ") -> true\n"),(index+2))
          Predication predS ts _ ->
              (((predSymStr predS) ++ "(" ++ (terms_str ts) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1) ++ "," ++ (terms_str ts) ++ 
              ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ "," ++ (terms_str ts) ++ 
              ") -> true\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk2 ++ "(" ++ (predSymStr predS) ++ "(" ++ (terms_str ts) ++
              ")," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk2 ++ "(true," ++ (term_str t1) ++ "," ++ (term_str t2) ++
              ") -> true\n"),(index +2))
          Negation (Predication predS ts _) _ ->
              (((predSymStr predS) ++ "(" ++ (terms_str ts) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1) ++ "," ++ (terms_str ts) ++ 
              ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ "," ++ (terms_str ts) ++ 
              ") -> false\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk2 ++ "(" ++ (predSymStr predS) ++ "(" ++ (terms_str ts) ++
              ")," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk2 ++ "(false," ++ (term_str t1) ++ "," ++ (term_str t2) ++
              ") -> true\n"),(index +2))
          Strong_equation t3 t4 _ ->
              (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1)++ "," ++ (term_str t3) ++ 
              "," ++ (term_str t4) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ","++ (term_str t3) ++ 
              "," ++ (term_str t4) ++ ") -> " ++ "true\n" ++ 
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t3)++ "," ++ (term_str t1) ++ 
              "," ++ (term_str t2) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t4) ++ ","++ (term_str t1) ++ 
              "," ++ (term_str t2) ++ ") -> " ++ "true\n"),(index + 2))
          Negation (Strong_equation t3 t4 _) _ ->
              (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1)++ "," ++ (term_str t3) ++ 
              "," ++ (term_str t4) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ","++ (term_str t3) ++ 
              "," ++ (term_str t4) ++ ") -> " ++ "false\n" ++ 
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk1 ++ "(eq(" ++ (term_str t3)++ "," ++ (term_str t4) ++
              ")," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk1 ++ "(false," ++ (term_str t1) ++ 
              "," ++ (term_str t2) ++ ") -> " ++ "true\n"),(index + 2))
          Existl_equation t3 t4 _ ->
              (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1)++ "," ++ (term_str t3) ++ 
              "," ++ (term_str t4) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ","++ (term_str t3) ++ 
              "," ++ (term_str t4) ++ ") -> " ++ "true\n" ++ 
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t3)++ "," ++ (term_str t1) ++ 
              "," ++ (term_str t2) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t4) ++ ","++ (term_str t1) ++ 
              "," ++ (term_str t2) ++ ") -> " ++ "true\n"),(index + 2))
          Negation (Existl_equation t3 t4 _) _ ->
              (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1)++ "," ++ (term_str t3) ++ 
              "," ++ (term_str t4) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ","++ (term_str t3) ++ 
              "," ++ (term_str t4) ++ ") -> " ++ "false\n" ++ 
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk1 ++ "(eq(" ++ (term_str t3)++ "," ++ (term_str t4) ++
              ")," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk1 ++ "(false," ++ (term_str t1) ++ 
              "," ++ (term_str t2) ++ ") -> " ++ "true\n"),(index + 2))
          _ -> error "CASL.CCC.TerminationProof.<equiv_str_str>"
    Equivalence (Existl_equation t1 t2 _) f1 _ ->
        case (quanti f1) of
          Conjunction _ _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_str t1) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ") -> true\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk2 ++ "(" ++ (axiom_substr (quanti f1)) ++ "," ++
              (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk2 ++ "(true," ++ (term_str t1) ++ "," ++
              (term_str t2) ++ ") -> true\n"),(index+2))
          Negation (Conjunction _ _) _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_str t1) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ") -> false\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk2 ++ "(" ++ (axiom_substr (quanti f1)) ++ "," ++
              (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk2 ++ "(false," ++ (term_str t1) ++ "," ++
              (term_str t2) ++ ") -> true\n"),(index+2))
          Disjunction _ _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_str t1) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ") -> true\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk2 ++ "(" ++ (axiom_substr (quanti f1)) ++ "," ++
              (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk2 ++ "(true," ++ (term_str t1) ++ "," ++
              (term_str t2) ++ ") -> true\n"),(index+2))
          Negation (Disjunction _ _) _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_str t1) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ") -> false\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk2 ++ "(" ++ (axiom_substr (quanti f1)) ++ "," ++
              (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk2 ++ "(false," ++ (term_str t1) ++ "," ++
              (term_str t2) ++ ") -> true\n"),(index+2))
          Predication predS ts _ ->
              (((predSymStr predS) ++ "(" ++ (terms_str ts) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1) ++ "," ++ (terms_str ts) ++ 
              ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ "," ++ (terms_str ts) ++ 
              ") -> true\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk2 ++ "(" ++ (predSymStr predS) ++ "(" ++ (terms_str ts) ++
              ")," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk2 ++ "(true," ++ (term_str t1) ++ "," ++ (term_str t2) ++
              ") -> true\n"),(index +2))
          Negation (Predication predS ts _) _ ->
              (((predSymStr predS) ++ "(" ++ (terms_str ts) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1) ++ "," ++ (terms_str ts) ++ 
              ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ "," ++ (terms_str ts) ++ 
              ") -> false\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk2 ++ "(" ++ (predSymStr predS) ++ "(" ++ (terms_str ts) ++
              ")," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk2 ++ "(false," ++ (term_str t1) ++ "," ++ (term_str t2) ++
              ") -> true\n"),(index +2))
          Strong_equation t3 t4 _ ->
              (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1)++ "," ++ (term_str t3) ++ 
              "," ++ (term_str t4) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ","++ (term_str t3) ++ 
              "," ++ (term_str t4) ++ ") -> " ++ "true\n" ++ 
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t3)++ "," ++ (term_str t1) ++ 
              "," ++ (term_str t2) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t4) ++ ","++ (term_str t1) ++ 
              "," ++ (term_str t2) ++ ") -> " ++ "true\n"),(index + 2))
          Negation (Strong_equation t3 t4 _) _ ->
              (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1)++ "," ++ (term_str t3) ++ 
              "," ++ (term_str t4) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ","++ (term_str t3) ++ 
              "," ++ (term_str t4) ++ ") -> " ++ "false\n" ++ 
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk1 ++ "(eq(" ++ (term_str t3)++ "," ++ (term_str t4) ++
              ")," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk1 ++ "(false," ++ (term_str t1) ++ 
              "," ++ (term_str t2) ++ ") -> " ++ "true\n"),(index + 2))
          Existl_equation t3 t4 _ ->
              (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1)++ "," ++ (term_str t3) ++ 
              "," ++ (term_str t4) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ","++ (term_str t3) ++ 
              "," ++ (term_str t4) ++ ") -> " ++ "true\n" ++ 
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t3)++ "," ++ (term_str t1) ++ 
              "," ++ (term_str t2) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t4) ++ ","++ (term_str t1) ++ 
              "," ++ (term_str t2) ++ ") -> " ++ "true\n"),(index + 2))
          Negation (Existl_equation t3 t4 _) _ ->
              (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1)++ "," ++ (term_str t3) ++ 
              "," ++ (term_str t4) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ","++ (term_str t3) ++ 
              "," ++ (term_str t4) ++ ") -> " ++ "false\n" ++ 
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk1 ++ "(eq(" ++ (term_str t3)++ "," ++ (term_str t4) ++
              ")," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk1 ++ "(false," ++ (term_str t1) ++ 
              "," ++ (term_str t2) ++ ") -> " ++ "true\n"),(index + 2))
          _ -> error "CASL.CCC.TerminationProof.<equiv_str_exi>"
    _ -> error "CASL.CCC.TerminationProof.<equiv_str>"
  where fk1 = "af" ++ (show index)
        fk2 = "af" ++ (show $ index + 1)
 

impli_equiv_str :: Int -> FORMULA f -> (String,Int)
impli_equiv_str index f = 
  case (quanti f) of
    Implication _ _ _ _ -> impli_str index f
    Equivalence _ _ _ -> equiv_str index f
    _ -> error "CASL.CCC.TerminationProof.<impli_equiv_str2>"


{- transform a axiom to str (f_str)
-}
axiom_str :: FORMULA f -> String
axiom_str f = 
  case (quanti f) of
    Quantification _ _ f' _ -> axiom_str f'
    Conjunction fs _ -> 
        conj_str fs ++ " -> true"
    Disjunction fs _ -> 
        disj_str fs ++ " -> true"
    Negation f' _ ->
        case f' of
          Conjunction fs _ ->
              conj_str fs ++ " -> false"
          Disjunction fs _ ->
              disj_str fs ++ " -> false"
          Predication p_s ts _ -> 
              ((predSymStr p_s) ++ "(" ++ (terms_str ts) ++ ") -> false")
          Existl_equation t1 t2 _ -> 
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> false"
          Strong_equation t1 t2 _ -> 
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> false"
          Definedness _ _ -> ""           -- not implement
          _ -> error "CASL.CCC.TerminationProof.<Axioms_Negation>"
    True_atom _ -> 
        error "CASL.CCC.TerminationProof.<Axioms_True>"     
    False_atom _ -> 
        error "CASL.CCC.TerminationProof.<Axioms_False>"
    Predication p_s ts _ -> 
        ((predSymStr p_s) ++ "(" ++ (terms_str ts) ++ ") -> true")
    Definedness _ _ -> 
        error "CASL.CCC.TerminationProof.<Axioms_Definedness>"
    Existl_equation t1 t2 _ -> 
        (term_str t1) ++ " -> " ++ (term_str t2)
    Strong_equation t1 t2 _ -> 
        (term_str t1) ++ " -> " ++ (term_str t2)                   
    _ -> error "CASL.CCC.TerminationProof.<Axioms>"
--  where termsStr ts = if null ts 
--                    then error "CASL.CCC.TerminationProof.axiom_str"
--                    else tail $ concat $ map (\s->","++s) $ map term_str ts


{- transform a axiom to substr
-}
axiom_substr :: FORMULA f -> String
axiom_substr f = 
  case (quanti f) of
    Quantification _ _ f' _ -> axiom_substr f'
    Conjunction fs _ -> 
        conj_str fs
    Disjunction fs _ -> 
        disj_str fs
    Negation f' _ ->
        case f' of
          Conjunction fs _ ->
              "not(" ++ conj_str fs ++ ")"
          Disjunction fs _ ->
              "not(" ++ disj_str fs ++ ")"
          Predication p_s ts _ -> 
              "not(" ++ (predSymStr p_s) ++ "(" ++ (terms_str ts) ++ "))"
          Existl_equation t1 t2 _ -> 
              "not(eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ "))"
          Strong_equation t1 t2 _ -> 
              "not(eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ "))"
          Definedness _ _ -> 
              ""           -- not implement
          _ -> error "CASL.CCC.TerminationProof.str_substr.<Negation>"
    True_atom _ -> 
        "true"     
    False_atom _ -> 
        "false"
    Predication p_s ts _ -> 
        (predSymStr p_s) ++ "(" ++ (terms_str ts) ++ ")"
    Definedness _ _ -> 
        error "CASL.CCC.TerminationProof.<Axioms_Definedness>"
    Existl_equation t1 t2 _ -> 
        "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")"
    Strong_equation t1 t2 _ -> 
        "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")"
    _ -> error "CASL.CCC.TerminationProof.axiom_substr.<Axioms>"


conj_str :: [FORMULA f] -> String
conj_str fs =
  if length fs == 2 then ("and(" ++ (axiom_substr $ head fs) ++ "," ++
                                   (axiom_substr $ last fs) ++ ")")
  else ("and(" ++ (axiom_str $ head fs) ++ "," ++
                  (conj_str $ tail fs) ++ ")")

disj_str :: [FORMULA f] -> String
disj_str fs =
  if length fs == 2 then ("or(" ++ (axiom_substr $ head fs) ++ "," ++
                                  (axiom_substr $ last fs) ++ ")")
  else ("or(" ++ (axiom_str $ head fs) ++ "," ++
                 (conj_str $ tail fs) ++ ")")


-- | transform a term to string
term_str :: TERM f -> String
term_str t = 
  case (term t) of
    Qual_var var _ _ -> tokStr var
    Application (Op_name opn) _ _ ->
        idStr opn
    Application (Qual_op_name opn _ _) ts _ -> 
        if null ts then (idStr opn)
        else ((idStr opn) ++ "(" ++ 
             (tail $ concat $ map (\s->","++s) $ map term_str ts)++")")
    Conditional t1 f t2 _ -> 
        ("when_else("++(term_str t1)++","++
         (t_f_str f)++","++(term_str t2)++")")  
    _ -> error "CASL.CCC.TerminationProof.<Term>"
  where t_f_str f=case f of                     --  condition of term
                    Strong_equation t1 t2 _ -> 
                        ("eq("++(term_str t1)++","++(term_str t2)++")")
                    Predication ps ts _ ->
                        ((predSymStr ps) ++ "(" ++
                        (terms_str ts) ++ ")")
                    _ -> error "CASL.CCC.TerminationProof.<Term-Formula>"


-- | transform a group of terms to string
terms_str :: [TERM f] -> String
terms_str ts = 
    if null ts then ""
    else tail $ concat $ map (\s->","++s) $ map term_str ts



