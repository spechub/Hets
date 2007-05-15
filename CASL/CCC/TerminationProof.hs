{- | 
Module      :  $Header$
Description :  termination proofs for equation systems, using AProve
Copyright   :  (c) Mingyi Liu and Till Mossakowski and Uni Bremen 2004-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  xinga@tzi.de
Stability   :  provisional
Portability :  portable

Termination proofs for equation systems, using AProve
-}

module CASL.CCC.TerminationProof where

import CASL.ToDoc ()
import CASL.AS_Basic_CASL       
import Common.AS_Annotation
import Common.DocUtils
import CASL.CCC.TermFormula
import Common.Id
import System.Cmd
import System.IO.Unsafe
import Debug.Trace

import System.Environment

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
    | otherwise = error "CASL.CCC.TerminationProof.<terminationProof>"
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
    --  transform all axioms except implication and equivalence to string
    axiomStr axs str
        | null axs = str
        | otherwise = 
            axiomStr (tail axs) (str ++ (axiom_str $ (head axs)) ++ "\n")
    impli_equiv = filter is_impli_equiv all_axioms
    n_impli_equiv = filter (not.is_impli_equiv) all_axioms
    auxAxstr afs str
        | null afs = str
        | otherwise =
              auxAxstr (tail afs) (str ++ (impli_equiv_str (head afs)))
    axAux = auxAxstr impli_equiv ""  
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
                --system ("java -jar CASL/Termination/AProVE.jar -u cli -m " ++
                --        "wst -p plain " ++ 
                --        ipath ++ " | head -n 1 > " ++ opath)
                aprovePath <- catch (getEnv "HETS_APROVE" >>= (\v -> return v)) 
                             (\_ -> return "CASL/Termination/AProVE.jar")
                system ("java -jar " ++ aprovePath ++ " -u cli -m " ++
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


-- | transform Implication to string
impli_str :: FORMULA f -> String
impli_str f =
  case (quanti f) of
    Implication f1 f2 False _ -> (axiom_substr (quanti f2)) ++ " -> true | " ++
                                 (axiom_substr (quanti f1)) ++ " -> true\n"
    Implication (Predication predS1 ts1 _) f1 _ _ ->
        case (quanti f1) of
          Conjunction _ _ ->
              ((axiom_substr (quanti f1)) ++ " -> true | " ++ 
              (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ ") -> true\n")
          Negation (Conjunction _ _) _ ->
              ((axiom_substr (quanti f1)) ++ " -> false | " ++ 
              (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ ") -> true\n")
          Disjunction _ _ ->
              ((axiom_substr (quanti f1)) ++ " -> true | " ++ 
              (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ ") -> true\n")
          Negation (Disjunction _ _) _ ->
              ((axiom_substr (quanti f1)) ++ " -> false | " ++ 
              (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ ") -> true\n")
          Predication predS2 ts2 _ ->
              ((predSymStr predS2) ++ "(" ++ (terms_str ts2) ++ 
              ") -> true | " ++ (predSymStr predS1) ++ "(" ++ 
              (terms_str ts1) ++ ") -> true\n")
          Negation (Predication predS2 ts2 _) _ ->
              ((predSymStr predS2) ++ "(" ++ (terms_str ts2) ++ 
              ") -> false | " ++ (predSymStr predS1) ++ "(" ++ 
              (terms_str ts1) ++ ") -> true\n")
          Strong_equation t1 t2 _ ->
              ("eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> true | " ++ (predSymStr predS1) ++ "(" ++ 
              (terms_str ts1) ++ ") -> true\n")
          Negation (Strong_equation t1 t2 _) _ ->
              ("eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> false | " ++ (predSymStr predS1) ++ "(" ++ 
              (terms_str ts1) ++ ") -> true\n")
          Existl_equation t1 t2 _ ->
              ("eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> true | " ++ (predSymStr predS1) ++ "(" ++ 
              (terms_str ts1) ++ ") -> true\n")
          Negation (Existl_equation t1 t2 _) _ ->
              ("eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> false | " ++ (predSymStr predS1) ++ "(" ++ 
              (terms_str ts1) ++ ") -> true\n")
          Equivalence (Predication predS2 ts2 _) f2 _ ->
              case (quanti f2) of
                Conjunction _ _ ->
                    ((axiom_substr (quanti f2)) ++ " -> true | " ++ 
                    (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ") -> true, " ++ 
                    (predSymStr predS2) ++ "(" ++ 
                    (terms_str ts2) ++ ") -> true\n")
                Negation (Conjunction _ _) _ ->
                    ((axiom_substr (quanti f2)) ++ " -> false | " ++ 
                    (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ") -> true, " ++ 
                    (predSymStr predS2) ++ "(" ++ 
                    (terms_str ts2) ++ ") -> true\n")
                Disjunction _ _ ->
                    ((axiom_substr (quanti f2)) ++ " -> true | " ++ 
                    (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ") -> true, " ++ 
                    (predSymStr predS2) ++ "(" ++ 
                    (terms_str ts2) ++ ") -> true\n")
                Negation (Disjunction _ _) _ ->
                    ((axiom_substr (quanti f2)) ++ " -> false | " ++ 
                    (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ") -> true, " ++ 
                    (predSymStr predS2) ++ "(" ++ 
                    (terms_str ts2) ++ ") -> true\n")
                Predication predS3 ts3 _ ->
                    ((predSymStr predS3) ++ "(" ++ (terms_str ts3) ++ 
                    ") -> true | "++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
                    ") -> true, " ++ 
                    (predSymStr predS2) ++ "(" ++ (terms_str ts2) ++
                    ") -> true\n")
                Negation (Predication predS3 ts3 _) _ ->
                    ((predSymStr predS3) ++ "(" ++ (terms_str ts3) ++ 
                    ") -> false | "++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
                    ") -> true, " ++ 
                    (predSymStr predS2) ++ "(" ++ (terms_str ts2) ++
                    ") -> true\n")
                Strong_equation t1 t2 _ ->
                    ("eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
                    ") -> true | " ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
                    ") -> true, " ++ 
                    (predSymStr predS2) ++ "(" ++ (terms_str ts2) ++
                    ") -> true\n")
                Negation (Strong_equation t1 t2 _) _ ->
                    ("eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
                    ") -> false | " ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
                    ") -> true, " ++ 
                    (predSymStr predS2) ++ "(" ++ (terms_str ts2) ++
                    ") -> true\n")
                Existl_equation t1 t2 _ ->
                    ("eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
                    ") -> true | " ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
                    ") -> true, " ++ 
                    (predSymStr predS2) ++ "(" ++ (terms_str ts2) ++
                    ") -> true\n")
                Negation (Existl_equation t1 t2 _) _ ->
                    ("eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
                    ") -> false | " ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
                    ") -> true, " ++ 
                    (predSymStr predS2) ++ "(" ++ (terms_str ts2) ++
                    ") -> true\n")
                _ -> error "CASL.CCC.TerminationProof.<impli_str_p_eq_p>"
          Equivalence (Strong_equation t1 t2 _) f2 _ ->
              case (quanti f2) of
                Conjunction _ _ ->
                    ((axiom_substr (quanti f2)) ++ " -> true | " ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
                    ") -> true, " ++ (term_str t1) ++ " -> " ++ 
                    (term_str t2) ++ "\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++
                    ") -> true | " ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
                    ") -> true, " ++ (axiom_substr (quanti f2)) ++
                    " -> true\n")
                Negation (Conjunction _ _) _ ->
                    ((axiom_substr (quanti f2)) ++ " -> false | " ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
                    ") -> true, " ++ (term_str t1) ++ " -> " ++ 
                    (term_str t2) ++ "\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++
                    ") -> true | " ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
                    ") -> true, " ++ (axiom_substr (quanti f2)) ++
                    " -> false\n")
                Disjunction _ _ ->
                    ((axiom_substr (quanti f2)) ++ " -> true | " ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
                    ") -> true, " ++ (term_str t1) ++ " -> " ++
                    (term_str t2) ++ "\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++
                    ") -> true | " ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
                    ") -> true, " ++ (axiom_substr (quanti f2)) ++
                    " -> true\n")
                Negation (Disjunction _ _) _ ->
                    ((axiom_substr (quanti f2)) ++ " -> false | " ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
                    ") -> true, " ++ (term_str t1) ++ " -> " ++ 
                    (term_str t2) ++ "\n" ++ 
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++
                    ") -> true | " ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
                    ") -> true, " ++ (axiom_substr (quanti f2)) ++
                    " -> false\n")
                Predication predS2 ts2 _ ->
                    ((predSymStr predS2) ++ "(" ++ (terms_str ts2) ++ 
                    ") -> true | " ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
                    ") -> true, " ++ (term_str t1) ++ " -> " ++
                    (term_str t2) ++ "\n" ++ 
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++
                    ") -> true | " ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
                    ") -> true, " ++ (predSymStr predS2) ++ "(" ++
                    (terms_str ts2) ++ ") -> true\n")
                Negation (Predication predS2 ts2 _) _ ->
                    ((predSymStr predS2) ++ "(" ++ (terms_str ts2) ++ 
                    ") -> false | " ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
                    ") -> true, " ++ (term_str t1) ++ " -> " ++
                    (term_str t2) ++ "\n" ++ 
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++
                    ") -> true | " ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
                    ") -> true, " ++ (predSymStr predS2) ++ "(" ++
                    (terms_str ts2) ++ ") -> false\n")
                Strong_equation t3 t4 _ ->
                    ("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true | " ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ") -> true, " ++ (term_str t1) ++ 
                    " -> " ++ (term_str t2) ++ "\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
                    ") -> true | " ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ") -> true, " ++ (term_str t3) ++ 
                    " -> " ++ (term_str t4) ++ "\n")
                Negation (Strong_equation t3 t4 _) _ ->
                    ("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> false | " ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ") -> true, " ++ (term_str t1) ++ 
                    " -> " ++ (term_str t2) ++ "\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
                    ") -> true | " ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ") -> true, eq(" ++ (term_str t3) ++ 
                    "," ++ (term_str t4) ++ ") -> false\n")
                Existl_equation t3 t4 _ ->
                    ("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true | " ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ") -> true, " ++ (term_str t1) ++ 
                    " -> " ++ (term_str t2) ++ "\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
                    ") -> true | " ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ") -> true, " ++ (term_str t3) ++ 
                    " -> " ++ (term_str t4) ++ "\n")
                Negation (Existl_equation t3 t4 _) _ ->
                    ("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> false | " ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ") -> true, " ++ (term_str t1) ++ 
                    " -> " ++ (term_str t2) ++ "\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
                    ") -> true | " ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ") -> true, eq(" ++ (term_str t3) ++ 
                    "," ++ (term_str t4) ++ ") -> false\n")                   
                _ -> error "CASL.CCC.TerminationProof.<impli_str_p_eq_str>"
          Equivalence (Existl_equation t1 t2 _) f2 _ ->
              case (quanti f2) of
                Conjunction _ _ ->
                    ((axiom_substr (quanti f2)) ++ " -> true | " ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
                    ") -> true, " ++ (term_str t1) ++ " -> " ++ 
                    (term_str t2) ++ "\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++
                    ") -> true | " ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
                    ") -> true, " ++ (axiom_substr (quanti f2)) ++
                    " -> true\n")
                Negation (Conjunction _ _) _ ->
                    ((axiom_substr (quanti f2)) ++ " -> false | " ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
                    ") -> true, " ++ (term_str t1) ++ " -> " ++ 
                    (term_str t2) ++ "\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++
                    ") -> true | " ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
                    ") -> true, " ++ (axiom_substr (quanti f2)) ++
                    " -> false\n")
                Disjunction _ _ ->
                    ((axiom_substr (quanti f2)) ++ " -> true | " ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
                    ") -> true, " ++ (term_str t1) ++ " -> " ++
                    (term_str t2) ++ "\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++
                    ") -> true | " ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
                    ") -> true, " ++ (axiom_substr (quanti f2)) ++
                    " -> true\n")
                Negation (Disjunction _ _) _ ->
                    ((axiom_substr (quanti f2)) ++ " -> false | " ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
                    ") -> true, " ++ (term_str t1) ++ " -> " ++ 
                    (term_str t2) ++ "\n" ++ 
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++
                    ") -> true | " ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
                    ") -> true, " ++ (axiom_substr (quanti f2)) ++
                    " -> false\n")
                Predication predS2 ts2 _ ->
                    ((predSymStr predS2) ++ "(" ++ (terms_str ts2) ++ 
                    ") -> true | " ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
                    ") -> true, " ++ (term_str t1) ++ " -> " ++
                    (term_str t2) ++ "\n" ++ 
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++
                    ") -> true | " ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
                    ") -> true, " ++ (predSymStr predS2) ++ "(" ++
                    (terms_str ts2) ++ ") -> true\n")
                Negation (Predication predS2 ts2 _) _ ->
                    ((predSymStr predS2) ++ "(" ++ (terms_str ts2) ++ 
                    ") -> false | " ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
                    ") -> true, " ++ (term_str t1) ++ " -> " ++
                    (term_str t2) ++ "\n" ++ 
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++
                    ") -> true | " ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
                    ") -> true, " ++ (predSymStr predS2) ++ "(" ++
                    (terms_str ts2) ++ ") -> false\n")
                Strong_equation t3 t4 _ ->
                    ("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true | " ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ") -> true, " ++ (term_str t1) ++ 
                    " -> " ++ (term_str t2) ++ "\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
                    ") -> true | " ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ") -> true, " ++ (term_str t3) ++ 
                    " -> " ++ (term_str t4) ++ "\n")
                Negation (Strong_equation t3 t4 _) _ ->
                    ("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> false | " ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ") -> true, " ++ (term_str t1) ++ 
                    " -> " ++ (term_str t2) ++ "\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
                    ") -> true | " ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ") -> true, eq(" ++ (term_str t3) ++ 
                    "," ++ (term_str t4) ++ ") -> false\n")
                Existl_equation t3 t4 _ ->
                    ("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true | " ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ") -> true, " ++ (term_str t1) ++ 
                    " -> " ++ (term_str t2) ++ "\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
                    ") -> true | " ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ") -> true, " ++ (term_str t3) ++ 
                    " -> " ++ (term_str t4) ++ "\n")
                Negation (Existl_equation t3 t4 _) _ ->
                    ("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> false | " ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ") -> true, " ++ (term_str t1) ++ 
                    " -> " ++ (term_str t2) ++ "\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
                    ") -> true | " ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ") -> true, eq(" ++ (term_str t3) ++ 
                    "," ++ (term_str t4) ++ ") -> false\n")  
                _ -> error "CASL.CCC.TerminationProof.<impli_str_p_eq_ex>"
          _ -> error "CASL.CCC.TerminationProof.<impli_str_p>"
    Implication (Strong_equation t1 t2 _) f1 _ _ ->
        case (quanti f1) of
          Conjunction _ _ ->
              ((axiom_substr (quanti f1)) ++ " -> true | " ++ 
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n")
          Negation (Conjunction _ _) _ ->
              ((axiom_substr (quanti f1)) ++ " -> false | " ++ 
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n")
          Disjunction _ _ ->
              ((axiom_substr (quanti f1)) ++ " -> true | " ++ 
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n")
          Negation (Disjunction _ _) _ ->
              ((axiom_substr (quanti f1)) ++ " -> false | " ++ 
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n")
          Predication predS ts _ ->
              ((predSymStr predS) ++ "(" ++ (terms_str ts) ++ ") -> true | " ++
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n")
          Negation (Predication predS ts _) _ ->
              ((predSymStr predS) ++ "(" ++ (terms_str ts) ++ ") -> false | "++
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n")
          Strong_equation t3 t4 _ ->
              ("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
              ") -> true | " ++
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n")
          Negation (Strong_equation t3 t4 _) _ ->
              ("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
              ") -> false | " ++
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n")
          Existl_equation t3 t4 _ ->
              ("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
              ") -> true | " ++
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n")
          Negation (Existl_equation t3 t4 _) _ ->
              ("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
              ") -> false | " ++
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n")
          Equivalence (Predication predS1 ts1 _) f2 _->
              case (quanti f2) of
                Conjunction _ _ ->
                    ((axiom_substr (quanti f2)) ++ " -> true | " ++ 
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
                    ") -> true\n")
                Negation (Conjunction _ _) _ ->
                    ((axiom_substr (quanti f2)) ++ " -> false | " ++ 
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
                    ") -> true\n")
                Disjunction _ _ ->
                    ((axiom_substr (quanti f2)) ++ " -> true | " ++ 
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
                    ") -> true\n")
                Negation (Disjunction _ _) _ ->
                    ((axiom_substr (quanti f2)) ++ " -> false | " ++ 
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
                    ") -> true\n")
                Predication predS2 ts2 _ ->
                    ((predSymStr predS2) ++ "(" ++ (terms_str ts2) ++ 
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
                    ") -> true\n")
                Negation (Predication predS2 ts2 _) _ ->
                    ((predSymStr predS2) ++ "(" ++ (terms_str ts2) ++ 
                    ") -> false | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
                    ") -> true\n")
                Strong_equation t3 t4 _ ->
                    ("eq(" ++  (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
                    ") -> true\n")
                Negation (Strong_equation t3 t4 _) _ ->
                    ("eq(" ++  (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> false | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
                    ") -> true\n")
                Existl_equation t3 t4 _ ->
                    ("eq(" ++  (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
                    ") -> true\n")
                Negation (Existl_equation t3 t4 _) _ ->
                    ("eq(" ++  (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> false | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
                    ") -> true\n")
                _ -> error "CASL.CCC.TerminationProof.<impli_str_str_eq_p>"
          Equivalence (Strong_equation t3 t4 _) f2 _->
              case (quanti f2) of
                Conjunction _ _ ->
                    ((axiom_substr (quanti f2)) ++ " -> true | " ++ 
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (axiom_substr (quanti f2)) ++ " -> true\n")
                Negation (Conjunction _ _) _ ->
                    ((axiom_substr (quanti f2)) ++ " -> false | " ++ 
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (axiom_substr (quanti f2)) ++ " -> false\n")
                Disjunction _ _ ->
                    ((axiom_substr (quanti f2)) ++ " -> true | " ++ 
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (axiom_substr (quanti f2)) ++ " -> true\n")
                Negation (Disjunction _ _) _ ->
                    ((axiom_substr (quanti f2)) ++ " -> false | " ++ 
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (axiom_substr (quanti f2)) ++ " -> false\n")
                Predication predS ts _ ->
                    ((predSymStr predS) ++ "(" ++ (terms_str ts) ++ 
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (predSymStr predS) ++ "(" ++ (terms_str ts) ++ 
                    ") -> true\n")
                Negation (Predication predS ts _) _ ->
                    ((predSymStr predS) ++ "(" ++ (terms_str ts) ++ 
                    ") -> false | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (predSymStr predS) ++ "(" ++ (terms_str ts) ++ 
                    ") -> false\n")
                Strong_equation t5 t6 _ ->
                    ("eq(" ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t5) ++ " -> " ++ (term_str t6) ++ "\n")
                Negation (Strong_equation t5 t6 _) _ ->
                    ("eq(" ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> false | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", eq(" ++
                    (term_str t5) ++ "," ++ (term_str t6) ++ ") -> false\n")
                Existl_equation t5 t6 _ ->
                    ("eq(" ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t5) ++ " -> " ++ (term_str t6) ++ "\n")
                Negation (Existl_equation t5 t6 _) _ ->
                    ("eq(" ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> false | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", eq(" ++
                    (term_str t5) ++ "," ++ (term_str t6) ++ ") -> false\n")
                _ -> error "CASL.CCC.TerminationProof.<impli_str_str_eq_str>"
          Equivalence (Existl_equation t3 t4 _) f2 _->
              case (quanti f2) of
                Conjunction _ _ ->
                    ((axiom_substr (quanti f2)) ++ " -> true | " ++ 
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (axiom_substr (quanti f2)) ++ " -> true\n")
                Negation (Conjunction _ _) _ ->
                    ((axiom_substr (quanti f2)) ++ " -> false | " ++ 
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (axiom_substr (quanti f2)) ++ " -> false\n")
                Disjunction _ _ ->
                    ((axiom_substr (quanti f2)) ++ " -> true | " ++ 
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (axiom_substr (quanti f2)) ++ " -> true\n")
                Negation (Disjunction _ _) _ ->
                    ((axiom_substr (quanti f2)) ++ " -> false | " ++ 
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (axiom_substr (quanti f2)) ++ " -> false\n")
                Predication predS ts _ ->
                    ((predSymStr predS) ++ "(" ++ (terms_str ts) ++ 
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (predSymStr predS) ++ "(" ++ (terms_str ts) ++ 
                    ") -> true\n")
                Negation (Predication predS ts _) _ ->
                    ((predSymStr predS) ++ "(" ++ (terms_str ts) ++ 
                    ") -> false | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (predSymStr predS) ++ "(" ++ (terms_str ts) ++ 
                    ") -> false\n")
                Strong_equation t5 t6 _ ->
                    ("eq(" ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t5) ++ " -> " ++ (term_str t6) ++ "\n")
                Negation (Strong_equation t5 t6 _) _ ->
                    ("eq(" ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> false | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", eq(" ++
                    (term_str t5) ++ "," ++ (term_str t6) ++ ") -> false\n")
                Existl_equation t5 t6 _ ->
                    ("eq(" ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t5) ++ " -> " ++ (term_str t6) ++ "\n")
                Negation (Existl_equation t5 t6 _) _ ->
                    ("eq(" ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> false | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", eq(" ++
                    (term_str t5) ++ "," ++ (term_str t6) ++ ") -> false\n")
                _ -> error "CASL.CCC.TerminationProof.<impli_str_str_eq_ex>"
          _ -> error "CASL.CCC.TerminationProof.<impli_str_str>"
    Implication (Existl_equation t1 t2 _) f1 _ _ ->
        case (quanti f1) of
          Conjunction _ _ ->
              ((axiom_substr (quanti f1)) ++ " -> true | " ++ 
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n")
          Negation (Conjunction _ _) _ ->
              ((axiom_substr (quanti f1)) ++ " -> false | " ++ 
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n")
          Disjunction _ _ ->
              ((axiom_substr (quanti f1)) ++ " -> true | " ++ 
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n")
          Negation (Disjunction _ _) _ ->
              ((axiom_substr (quanti f1)) ++ " -> false | " ++ 
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n")
          Predication predS ts _ ->
              ((predSymStr predS) ++ "(" ++ (terms_str ts) ++ ") -> true | " ++
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n")
          Negation (Predication predS ts _) _ ->
              ((predSymStr predS) ++ "(" ++ (terms_str ts) ++ ") -> false | "++
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n")
          Strong_equation t3 t4 _ ->
              ("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
              ") -> true | " ++
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n")
          Negation (Strong_equation t3 t4 _) _ ->
              ("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
              ") -> false | " ++
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n")
          Existl_equation t3 t4 _ ->
              ("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
              ") -> true | " ++
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n")
          Negation (Existl_equation t3 t4 _) _ ->
              ("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
              ") -> false | " ++
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n")
          Equivalence (Predication predS1 ts1 _) f2 _->
              case (quanti f2) of
                Conjunction _ _ ->
                    ((axiom_substr (quanti f2)) ++ " -> true | " ++ 
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
                    ") -> true\n")
                Negation (Conjunction _ _) _ ->
                    ((axiom_substr (quanti f2)) ++ " -> false | " ++ 
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
                    ") -> true\n")
                Disjunction _ _ ->
                    ((axiom_substr (quanti f2)) ++ " -> true | " ++ 
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
                    ") -> true\n")
                Negation (Disjunction _ _) _ ->
                    ((axiom_substr (quanti f2)) ++ " -> false | " ++ 
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
                    ") -> true\n")
                Predication predS2 ts2 _ ->
                    ((predSymStr predS2) ++ "(" ++ (terms_str ts2) ++ 
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
                    ") -> true\n")
                Negation (Predication predS2 ts2 _) _ ->
                    ((predSymStr predS2) ++ "(" ++ (terms_str ts2) ++ 
                    ") -> false | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
                    ") -> true\n")
                Strong_equation t3 t4 _ ->
                    ("eq(" ++  (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
                    ") -> true\n")
                Negation (Strong_equation t3 t4 _) _ ->
                    ("eq(" ++  (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> false | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
                    ") -> true\n")
                Existl_equation t3 t4 _ ->
                    ("eq(" ++  (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
                    ") -> true\n")
                Negation (Existl_equation t3 t4 _) _ ->
                    ("eq(" ++  (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> false | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
                    ") -> true\n")
                _ -> error "CASL.CCC.TerminationProof.<impli_str_ex_eq_p>"
          Equivalence (Strong_equation t3 t4 _) f2 _->
              case (quanti f2) of
                Conjunction _ _ ->
                    ((axiom_substr (quanti f2)) ++ " -> true | " ++ 
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (axiom_substr (quanti f2)) ++ " -> true\n")
                Negation (Conjunction _ _) _ ->
                    ((axiom_substr (quanti f2)) ++ " -> false | " ++ 
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (axiom_substr (quanti f2)) ++ " -> false\n")
                Disjunction _ _ ->
                    ((axiom_substr (quanti f2)) ++ " -> true | " ++ 
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (axiom_substr (quanti f2)) ++ " -> true\n")
                Negation (Disjunction _ _) _ ->
                    ((axiom_substr (quanti f2)) ++ " -> false | " ++ 
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (axiom_substr (quanti f2)) ++ " -> false\n")
                Predication predS ts _ ->
                    ((predSymStr predS) ++ "(" ++ (terms_str ts) ++ 
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (predSymStr predS) ++ "(" ++ (terms_str ts) ++ 
                    ") -> true\n")
                Negation (Predication predS ts _) _ ->
                    ((predSymStr predS) ++ "(" ++ (terms_str ts) ++ 
                    ") -> false | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (predSymStr predS) ++ "(" ++ (terms_str ts) ++ 
                    ") -> false\n")
                Strong_equation t5 t6 _ ->
                    ("eq(" ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t5) ++ " -> " ++ (term_str t6) ++ "\n")
                Negation (Strong_equation t5 t6 _) _ ->
                    ("eq(" ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> false | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", eq(" ++
                    (term_str t5) ++ "," ++ (term_str t6) ++ ") -> false\n")
                Existl_equation t5 t6 _ ->
                    ("eq(" ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t5) ++ " -> " ++ (term_str t6) ++ "\n")
                Negation (Existl_equation t5 t6 _) _ ->
                    ("eq(" ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> false | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", eq(" ++
                    (term_str t5) ++ "," ++ (term_str t6) ++ ") -> false\n")
                _ -> error "CASL.CCC.TerminationProof.<impli_str_ex_eq_str>"
          Equivalence (Existl_equation t3 t4 _) f2 _->
              case (quanti f2) of
                Conjunction _ _ ->
                    ((axiom_substr (quanti f2)) ++ " -> true | " ++ 
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (axiom_substr (quanti f2)) ++ " -> true\n")
                Negation (Conjunction _ _) _ ->
                    ((axiom_substr (quanti f2)) ++ " -> false | " ++ 
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (axiom_substr (quanti f2)) ++ " -> false\n")
                Disjunction _ _ ->
                    ((axiom_substr (quanti f2)) ++ " -> true | " ++ 
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (axiom_substr (quanti f2)) ++ " -> true\n")
                Negation (Disjunction _ _) _ ->
                    ((axiom_substr (quanti f2)) ++ " -> false | " ++ 
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (axiom_substr (quanti f2)) ++ " -> false\n")
                Predication predS ts _ ->
                    ((predSymStr predS) ++ "(" ++ (terms_str ts) ++ 
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (predSymStr predS) ++ "(" ++ (terms_str ts) ++ 
                    ") -> true\n")
                Negation (Predication predS ts _) _ ->
                    ((predSymStr predS) ++ "(" ++ (terms_str ts) ++ 
                    ") -> false | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (predSymStr predS) ++ "(" ++ (terms_str ts) ++ 
                    ") -> false\n")
                Strong_equation t5 t6 _ ->
                    ("eq(" ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t5) ++ " -> " ++ (term_str t6) ++ "\n")
                Negation (Strong_equation t5 t6 _) _ ->
                    ("eq(" ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> false | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", eq(" ++
                    (term_str t5) ++ "," ++ (term_str t6) ++ ") -> false\n")
                Existl_equation t5 t6 _ ->
                    ("eq(" ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t5) ++ " -> " ++ (term_str t6) ++ "\n")
                Negation (Existl_equation t5 t6 _) _ ->
                    ("eq(" ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> false | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", " ++
                    (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> true | " ++
                    (term_str t1) ++ " -> " ++ (term_str t2) ++ ", eq(" ++
                    (term_str t5) ++ "," ++ (term_str t6) ++ ") -> false\n")
                _ -> error "CASL.CCC.TerminationProof.<impli_str_ex_eq_ex>"
          _ -> error "CASL.CCC.TerminationProof.<impli_str_ex>"
    _ -> error "CASL.CCC.TerminationProof.<impli_str>"


-- | transform Equivalence to string: 
equiv_str :: FORMULA f -> String
equiv_str f =
  case (quanti f) of
    Equivalence (Predication predS1 ts1 _) f1 _ ->
        case (quanti f1) of
          Conjunction _ _ ->
              ((axiom_substr (quanti f1)) ++ " -> true | " ++ 
              (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ ") -> true\n")
          Negation (Conjunction _ _) _ ->
              ((axiom_substr (quanti f1)) ++ " -> false | " ++ 
              (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ ") -> true\n")
          Disjunction _ _ ->
              ((axiom_substr (quanti f1)) ++ " -> true | " ++ 
              (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ ") -> true\n")
          Negation (Disjunction _ _) _ ->
              ((axiom_substr (quanti f1)) ++ " -> false | " ++ 
              (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ ") -> true\n")
          Predication predS2 ts2 _ ->
              ((predSymStr predS2) ++ "(" ++ (terms_str ts2) ++ 
              ") -> true | " ++
              (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ ") -> true\n")
          Negation (Predication predS2 ts2 _) _ ->
              ((predSymStr predS2) ++ "(" ++ (terms_str ts2) ++ 
              ") -> false | " ++
              (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ ") -> true\n")
          Strong_equation t1 t2 _ -> 
              ("eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> true | " ++
              (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ ") -> true\n")
          Negation (Strong_equation t1 t2 _) _ ->
              ("eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> false | " ++
              (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ ") -> true\n")
          Existl_equation t1 t2 _ -> 
              ("eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> true | " ++
              (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ ") -> true\n")
          Negation (Existl_equation t1 t2 _) _ ->
              ("eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> false | " ++
              (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ ") -> true\n")
          _ -> error "CASL.CCC.TerminationProof.<equiv_str_pred>"
    Equivalence (Strong_equation t1 t2 _) f1 _ ->
        case (quanti f1) of
          Conjunction _ _ ->
              ((axiom_substr (quanti f1)) ++ " -> true | " ++ 
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> true | " ++
              (axiom_substr (quanti f1)) ++ " -> true\n")
          Negation (Conjunction _ _) _ ->
              ((axiom_substr (quanti f1)) ++ " -> false | " ++ 
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> true | " ++
              (axiom_substr (quanti f1)) ++ " -> false\n")
          Disjunction _ _ ->
              ((axiom_substr (quanti f1)) ++ " -> true | " ++ 
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> true | " ++
              (axiom_substr (quanti f1)) ++ " -> true\n")
          Negation (Disjunction _ _) _ ->
              ((axiom_substr (quanti f1)) ++ " -> false | " ++ 
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> true | " ++
              (axiom_substr (quanti f1)) ++ " -> false\n")
          Predication predS ts _ ->
              ((predSymStr predS) ++ "(" ++ (terms_str ts) ++ 
              ") -> true | " ++
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> true | " ++
              (predSymStr predS) ++ "(" ++ (terms_str ts) ++ ") -> true\n")
          Negation (Predication predS ts _) _ ->
              ((predSymStr predS) ++ "(" ++ (terms_str ts) ++ 
              ") -> false | " ++
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> true | " ++
              (predSymStr predS) ++ "(" ++ (terms_str ts) ++ ") -> false\n")
          Strong_equation t3 t4 _ ->
              ("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
              ") -> true | " ++
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> true | " ++
              (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n")
          Negation (Strong_equation t3 t4 _) _ ->
              ("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
              ") -> false | " ++
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> true | eq(" ++
              (term_str t3) ++ "," ++ (term_str t4) ++ ") -> false\n")
          Existl_equation t3 t4 _ ->
              ("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
              ") -> true | " ++
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> true | " ++
              (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n")
          Negation (Existl_equation t3 t4 _) _ ->
              ("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
              ") -> false | " ++
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> true | eq(" ++
              (term_str t3) ++ "," ++ (term_str t4) ++ ") -> false\n")
          _ -> error "CASL.CCC.TerminationProof.<equiv_str_str>"
    Equivalence (Existl_equation t1 t2 _) f1 _ ->
        case (quanti f1) of
          Conjunction _ _ ->
              ((axiom_substr (quanti f1)) ++ " -> true | " ++ 
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> true | " ++
              (axiom_substr (quanti f1)) ++ " -> true\n")
          Negation (Conjunction _ _) _ ->
              ((axiom_substr (quanti f1)) ++ " -> false | " ++ 
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> true | " ++
              (axiom_substr (quanti f1)) ++ " -> false\n")
          Disjunction _ _ ->
              ((axiom_substr (quanti f1)) ++ " -> true | " ++ 
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> true | " ++
              (axiom_substr (quanti f1)) ++ " -> true\n")
          Negation (Disjunction _ _) _ ->
              ((axiom_substr (quanti f1)) ++ " -> false | " ++ 
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> true | " ++
              (axiom_substr (quanti f1)) ++ " -> false\n")
          Predication predS ts _ ->
              ((predSymStr predS) ++ "(" ++ (terms_str ts) ++ 
              ") -> true | " ++
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> true | " ++
              (predSymStr predS) ++ "(" ++ (terms_str ts) ++ ") -> true\n")
          Negation (Predication predS ts _) _ ->
              ((predSymStr predS) ++ "(" ++ (terms_str ts) ++ 
              ") -> false | " ++
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> true | " ++
              (predSymStr predS) ++ "(" ++ (terms_str ts) ++ ") -> false\n")
          Strong_equation t3 t4 _ ->
              ("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
              ") -> true | " ++
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> true | " ++
              (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n")
          Negation (Strong_equation t3 t4 _) _ ->
              ("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
              ") -> false | " ++
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> true | eq(" ++
              (term_str t3) ++ "," ++ (term_str t4) ++ ") -> false\n")
          Existl_equation t3 t4 _ ->
              ("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
              ") -> true | " ++
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> true | " ++
              (term_str t3) ++ " -> " ++ (term_str t4) ++ "\n")
          Negation (Existl_equation t3 t4 _) _ ->
              ("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
              ") -> false | " ++
              (term_str t1) ++ " -> " ++ (term_str t2) ++ "\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> true | eq(" ++
              (term_str t3) ++ "," ++ (term_str t4) ++ ") -> false\n")
          _ -> error "CASL.CCC.TerminationProof.<equiv_str_ex>"
    _ -> error "CASL.CCC.TerminationProof.<equiv_str>"
 

impli_equiv_str :: FORMULA f -> String
impli_equiv_str f = 
  case (quanti f) of
    Implication _ _ _ _ -> impli_str f
    Equivalence _ _ _ -> equiv_str f
    _ -> error "CASL.CCC.TerminationProof.<impli_equiv_str2>"


-- | transform a axiom to string
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
        case t2 of
          Conditional tt1 ff tt2 _ ->
              (term_str t1) ++ " -> " ++ (term_str tt1) ++ " | " ++
              (axiom_substr ff) ++ " -> true\n" ++  
              (term_str t1) ++ " -> " ++ (term_str tt2) ++ " | " ++
              (axiom_substr ff) ++ " -> false\n"  
          _ -> (term_str t1) ++ " -> " ++ (term_str t2)
    Strong_equation t1 t2 _ -> 
        case t2 of
          Conditional tt1 ff tt2 _ ->
              (term_str t1) ++ " -> " ++ (term_str tt1) ++ " | " ++
              (axiom_substr ff) ++ " -> true\n" ++  
              (term_str t1) ++ " -> " ++ (term_str tt2) ++ " | " ++
              (axiom_substr ff) ++ " -> false\n"  
          _ -> (term_str t1) ++ " -> " ++ (term_str t2)              
    _ -> error "CASL.CCC.TerminationProof.<Axioms>"


-- | transform a axiom to substr
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


-- | transform the conjunctive formulas to string
conj_str :: [FORMULA f] -> String
conj_str fs =
  if length fs == 2 then ("and(" ++ (axiom_substr $ head fs) ++ "," ++
                                   (axiom_substr $ last fs) ++ ")")
  else ("and(" ++ (axiom_substr $ head fs) ++ "," ++
                  (conj_str $ tail fs) ++ ")")


-- | transform the disjunctive formulas to string
disj_str :: [FORMULA f] -> String
disj_str fs =
  if length fs == 2 then ("or(" ++ (axiom_substr $ head fs) ++ "," ++
                                  (axiom_substr $ last fs) ++ ")")
  else ("or(" ++ (axiom_substr $ head fs) ++ "," ++
                 (disj_str $ tail fs) ++ ")")


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
    _ -> error "CASL.CCC.TerminationProof.<term_str>"
  where t_f_str f=case f of                     --  condition of term
                    Strong_equation t1 t2 _ -> 
                        ("eq("++(term_str t1)++","++(term_str t2)++")")
                    Predication ps ts _ ->
                        ((predSymStr ps) ++ "(" ++
                        (terms_str ts) ++ ")")
                    _ -> error "CASL.CCC.TerminationProof.<term_str_cond>"


-- | transform a group of terms to string
terms_str :: [TERM f] -> String
terms_str ts = 
    if null ts then ""
    else tail $ concat $ map (\s->","++s) $ map term_str ts



