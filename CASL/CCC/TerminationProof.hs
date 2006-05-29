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
import Common.PrettyPrint
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

terminationProof :: (PosItem f, PrettyPrint f, Eq f) => 
                    [Named (FORMULA f)] -> Maybe Bool
terminationProof fsn 
    | null all_axioms = Just True
    | proof == "YES\n" = Just True
    | proof == "MAYBE\n" = Nothing
    | proof == "No\n" = Just False
    | otherwise = error "termination proof"
    where
    fs1 = map sentence (filter is_user_or_sort_gen fsn)
    fs = trace (showPretty fs1 "all formulars") fs1
    all_axioms1 = filter (\f->(not $ is_Sort_gen_ax f) &&
                              (not $ is_Membership f) &&
                              (not $ is_ex_quanti f) &&
                              (not $ is_Def f)) fs
    all_axioms = trace (showPretty all_axioms1 "Terminal_allAxiom") all_axioms1
    all_predSymbs = everyOnce $ concat $ map predSymbsOfAxiom all_axioms
    fconstrs = concat $ map constraintOfAxiom fs
    (_,constructors1,_) = recover_Sort_gen_ax fconstrs
    constructors = trace (showPretty constructors1 "Ocons") constructors1
                                                           -- old constructors
    l_Syms1 = map leadingSym $ filter isOp_Pred $ fs             
    l_Syms = trace (showPretty l_Syms1 "o_leading_Symbol") l_Syms1
                                                          -- old leading_Symbol
    op_Syms = concat $ map (\s-> case s of
                                   Just (Left op) -> [op]
                                   _ -> []) l_Syms
    --  build signature of operation together 
    opSignStr signs str                      
        | null signs = str
        | otherwise = opSignStr (tail signs) (str ++ 
                                              (opS_str $ head signs) ++ ";\n")
    --  build signature of predication together 
    predSignStr signs str                      
        | null signs = str
        | otherwise = 
            predSignStr (tail signs) (str ++ 
                                      (predS_str $ head signs) ++ ";\n")
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
    sighead = "let F = signature \"when_else : 3;\n" ++
                                  "eq : binary;\n" ++
                                  "and : binary;\n" ++
                                  "or : binary;\n" ++
                                  "not : unary;\n" ++ 
                                  "True,False : constant;\n"
    auxSigstr ies i str 
        | null ies = str
        | otherwise =  
              auxSigstr (tail ies) (snd $ last tmp) (str ++ 
                             (concat $ map (\s-> ((fst.fst) s) ++ 
                             (dimension $ ((snd.fst) s)) ++ ";\n") tmp))
            where tmp = sigAuxf (head ies) i
    sigAux = auxSigstr impli_equiv 1 ""
    auxAxstr afs i str
        | null afs = str
        | otherwise =
              auxAxstr (tail afs) (snd tmp) (str ++ (fst tmp))
            where tmp = impli_equiv_str i (head afs)
    axAux = auxAxstr impli_equiv 1 ""  
    varhead = "(VAR "
    axhead = "(RULES\n"
    c_sigs = (sighead ++ (opSignStr (everyOnce (constructors ++
                                                op_Syms)) "") ++
                         (predSignStr all_predSymbs "") ++
              sigAux ++ "\";\n")
    c_vars = (varhead ++ (varsStr (allVar $ map varOfAxiom $ 
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



{- transform Id to str
   because str these symbols '[' and ']' do not know, 
   these symbols are replaced by '|'       (idStrT)
-}
id_str :: Id -> String 
id_str _id = map (\s-> case s of
                            '[' -> '|'
                            ']' -> '|'
                            _ -> s) $ idStr _id


opSymStr :: OP_SYMB -> String 
opSymStr os = case os of
                Op_name on -> idStr on
                Qual_op_name on _ _ -> idStr on


predSymStr :: PRED_SYMB -> String
predSymStr ps = case ps of 
                  Pred_name pn -> idStr pn 
                  Qual_pred_name pn _ _ -> idStr pn


{- transform a term to str (termStr)
-}
term_str :: TERM f -> String
term_str t = 
  case (term t) of
    Qual_var var _ _ -> tokStr var
    Application (Op_name opn) _ _ ->
        id_str opn
    Application (Qual_op_name opn _ _) ts _ -> 
        if null ts then (id_str opn)
        else ((id_str opn) ++ "(" ++ 
             (tail $ concat $ map (\s->","++s) $ map term_str ts)++")")
    Conditional t1 f t2 _ -> 
        ("when_else("++(term_str t1)++","++
         (t_f_str f)++","++(term_str t2)++")")  
    _ -> error "CASL.CCC.TerminationProof.<Term>"
  where t_f_str f=case f of                     --  condition of term
                    Strong_equation t1 t2 _ -> 
                        ("eq("++(term_str t1)++","++(term_str t2)++")")
               --    Predication PRED_SYMB [TERM f] Range
                    Predication ps ts _ ->
                        ((predSymStr ps) ++ "(" ++
                        (terms_str ts) ++ ")")
                    _ -> error "CASL.CCC.TerminationProof.<Term-Formula>"


dimension :: Int -> String
dimension a = case a of
                0 -> " : constant"
                1 -> " : unary"
                2 -> " : binary"
                _ -> " : " ++ (show a)


{- transform OP_SYMB to Signature of str (opStr)
-}
opS_str :: OP_SYMB -> String
opS_str o_s = 
  case o_s of
    Qual_op_name op_n (Op_type _ a_sorts _ _) _ -> 
        ((id_str op_n) ++ (dimension $ length a_sorts))
    _ -> error "CASL.CCC.TerminationProof.<Signature_OP_SYMB: Op_name>"


{- transform PRED_SYMB to Signature of str (predStr)
-}
predS_str :: PRED_SYMB -> String
predS_str p_s = 
  case p_s of
    Qual_pred_name pred_n (Pred_type sts _) _ -> 
        ((id_str pred_n) ++ (dimension $ length sts))
    _ -> error "CASL.CCC.TerminationProof.<predS_str>"


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
                  U1(e,True,tt_1,...,tt_n) -> t
          --> X=e =>  f(tt_1,...,tt_n)=t => p(t_1,...,t_m)   --> 
                  p(t_1,...,t_m) -> U2(X,f(tt_1,...,tt_n),t_1,...,t_m)
                  U2(e,t,t_1,...,t_m) -> True 
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
              fk1 ++ "(True) -> True\n"),(index+1))
          Negation (Conjunction _ _) _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
              "))\n" ++
              fk1 ++ "(True) -> False\n"),(index+1))
          Disjunction _ _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
              "))\n" ++
              fk1 ++ "(True) -> True\n"),(index+1))
          Negation (Disjunction _ _) _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
              "))\n" ++
              fk1 ++ "(True) -> False\n"),(index+1))
          Predication predS2 ts2 _ ->
              (((predSymStr predS2) ++ "(" ++ (terms_str ts2) ++ ") -> " ++
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
              ")," ++ (terms_str ts2) ++ ")\n" ++
              fk1 ++ "(True," ++ (terms_str ts2) ++ ") -> True\n" ),
              (index+1))
          Negation (Predication predS2 ts2 _) _ ->
              (((predSymStr predS2) ++ "(" ++ (terms_str ts2) ++ ") -> " ++
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
              ")," ++ (terms_str ts2) ++ ")\n" ++
              fk1 ++ "(True," ++ (terms_str ts2) ++ ") -> False\n" ),
              (index+1))
          Strong_equation t1 t2 _ ->
              (("eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
              ")," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk1 ++ "(True," ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> True\n"),(index + 1))
          Negation (Strong_equation t1 t2 _) _ ->
              (("eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
              ")," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk1 ++ "(True," ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> False\n"),(index + 1))
          Existl_equation t1 t2 _ ->
              (("eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
              ")," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk1 ++ "(True," ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> True\n"),(index + 1))
          Negation (Existl_equation t1 t2 _) _ ->
              (("eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
              ")," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk1 ++ "(True," ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> False\n"),(index + 1))
          Equivalence (Predication predS2 ts2 _) f2 _ ->
              case (quanti f2) of
                Conjunction _ _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (predSymStr predS2) ++ "(" ++ 
                    (terms_str ts2) ++"))\n" ++
                    fk1 ++ "(True,True) -> True\n"),(index+1))
                Negation (Conjunction _ _) _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (predSymStr predS2) ++ "(" ++ 
                    (terms_str ts2) ++"))\n" ++
                    fk1 ++ "(True,True) -> False\n"),(index+1))
                Disjunction _ _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (predSymStr predS2) ++ "(" ++ 
                    (terms_str ts2) ++"))\n" ++
                    fk1 ++ "(True,True) -> True\n"),(index+1))
                Negation (Disjunction _ _) _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (predSymStr predS2) ++ "(" ++ 
                    (terms_str ts2) ++"))\n" ++
                    fk1 ++ "(True,True) -> False\n"),(index+1))
                Predication predS3 ts3 _ ->
                    (((predSymStr predS3)++"("++(terms_str ts3)++") -> "++
                    fk1++"("++(predSymStr predS1)++"("++(terms_str ts1) ++ 
                    ")," ++ (predSymStr predS2) ++ "(" ++ (terms_str ts2) ++
                    ")," ++ (terms_str ts3) ++ ")\n" ++
                    fk1++"(True,True,"++(terms_str ts3)++") -> True\n"),
                    (index +1))
                Negation (Predication predS3 ts3 _) _ ->
                    (((predSymStr predS3)++"("++(terms_str ts3)++") -> "++
                    fk1++"("++(predSymStr predS1)++"("++(terms_str ts1) ++ 
                    ")," ++ (predSymStr predS2) ++ "(" ++ (terms_str ts2) ++
                    ")," ++ (terms_str ts3) ++ ")\n" ++
                    fk1++"(True,True,"++(terms_str ts3)++") -> False\n"),
                    (index + 1))
                Strong_equation t1 t2 _ ->
                    (("eq("++(term_str t1)++","++(term_str t2)++") -> " ++
                    fk1++"("++(predSymStr predS1)++"("++(terms_str ts1)++
                    ")," ++ (predSymStr predS2) ++ "(" ++ (terms_str ts2) ++
                    "),"++(term_str t1)++","++(term_str t2)++")\n" ++
                    fk1++"(True,True,"++(term_str t1)++","++(term_str t2)++ 
                    ") -> True\n"),(index +1))
                Negation (Strong_equation t1 t2 _) _ ->
                    (("eq("++(term_str t1)++","++(term_str t2)++") -> " ++
                    fk1++"("++(predSymStr predS1)++"("++(terms_str ts1)++
                    ")," ++ (predSymStr predS2) ++ "(" ++ (terms_str ts2) ++
                    "),"++(term_str t1)++","++(term_str t2)++")\n" ++
                    fk1++"(True,True,"++(term_str t1)++","++(term_str t2)++ 
                    ") -> False\n"),(index +1))
                Existl_equation t1 t2 _ ->
                    (("eq("++(term_str t1)++","++(term_str t2)++") -> " ++
                    fk1++"("++(predSymStr predS1)++"("++(terms_str ts1)++
                    ")," ++ (predSymStr predS2) ++ "(" ++ (terms_str ts2) ++
                    "),"++(term_str t1)++","++(term_str t2)++")\n" ++
                    fk1++"(True,True,"++(term_str t1)++","++(term_str t2)++ 
                    ") -> True\n"),(index +1))
                Negation (Existl_equation t1 t2 _) _ ->
                    (("eq("++(term_str t1)++","++(term_str t2)++") -> " ++
                    fk1++"("++(predSymStr predS1)++"("++(terms_str ts1)++
                    ")," ++ (predSymStr predS2) ++ "(" ++ (terms_str ts2) ++
                    "),"++(term_str t1)++","++(term_str t2)++")\n" ++
                    fk1++"(True,True,"++(term_str t1)++","++(term_str t2)++ 
                    ") -> False\n"),(index +1))
                _ -> error "CASL.CCC.TerminationProof.<impli_str_p_eq_p>"
          Equivalence (Strong_equation t1 t2 _) f2 _ ->
              case (quanti f2) of
                Conjunction _ _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ ")\n" ++
                    fk1 ++ "(True," ++ (term_str t2) ++ ") -> True\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++
                    ") -> " ++ fk2 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (axiom_substr (quanti f2)) ++
                    "," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
                    fk2 ++ "(True,True," ++ (term_str t1) ++ "," ++ 
                    (term_str t2) ++ ") -> True\n"),(index+2))
                Negation (Conjunction _ _) _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ ")\n" ++
                    fk1 ++ "(True," ++ (term_str t2) ++ ") -> False\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++
                    ") -> " ++ fk2 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (axiom_substr (quanti f2)) ++
                    "," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
                    fk2 ++ "(True,False," ++ (term_str t1) ++ "," ++ 
                    (term_str t2) ++ ") -> True\n"),(index+2))
                Disjunction _ _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ ")\n" ++
                    fk1 ++ "(True," ++ (term_str t2) ++ ") -> True\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++
                    ") -> " ++ fk2 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (axiom_substr (quanti f2)) ++
                    "," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
                    fk2 ++ "(True,True," ++ (term_str t1) ++ "," ++ 
                    (term_str t2) ++ ") -> True\n"),(index+2))
                Negation (Disjunction _ _) _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ ")\n" ++
                    fk1 ++ "(True," ++ (term_str t2) ++ ") -> False\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++
                    ") -> " ++ fk2 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (axiom_substr (quanti f2)) ++
                    "," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
                    fk2 ++ "(True,False," ++ (term_str t1) ++ "," ++ 
                    (term_str t2) ++ ") -> True\n"),(index+2))
                Predication predS2 ts2 _ ->
                    (((predSymStr predS2) ++ "(" ++ (terms_str ts2) ++ 
                    ") ->" ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ "," ++
                    (terms_str ts2) ++ ")\n" ++
                    fk1 ++ "(True," ++ (term_str t2) ++ "," ++ 
                    (terms_str ts2) ++ ") -> True\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++
                    ") -> " ++ fk2 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (predSymStr predS2) ++ "(" ++
                    (terms_str ts2) ++ ")," ++ (term_str t1) ++ "," ++
                    (term_str t2) ++ ")\n" ++
                    fk2 ++ "(True,True," ++ (term_str t1) ++ "," ++
                    (term_str t2) ++ ") -> True\n"),(index+2))
                Negation (Predication predS2 ts2 _) _ ->
                    (((predSymStr predS2) ++ "(" ++ (terms_str ts2) ++ 
                    ") ->" ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ "," ++
                    (terms_str ts2) ++ ")\n" ++
                    fk1 ++ "(True," ++ (term_str t2) ++ "," ++ 
                    (terms_str ts2) ++ ") -> False\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++
                    ") -> " ++ fk2 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (predSymStr predS2) ++ "(" ++
                    (terms_str ts2) ++ ")," ++ (term_str t1) ++ "," ++
                    (term_str t2) ++ ")\n" ++
                    fk2 ++ "(True,False," ++ (term_str t1) ++ "," ++
                    (term_str t2) ++ ") -> True\n"),(index+2))
                Strong_equation t3 t4 _ ->
                    (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ "," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk1 ++ "(True," ++ (term_str t2) ++ "," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> True\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t3) ++ "," ++
                    (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
                    fk1 ++ "(True," ++ (term_str t4) ++ "," ++ 
                    (term_str t1) ++ "," ++ (term_str t2) ++ ") -> True\n"),
                    (index+2))
                Negation (Strong_equation t3 t4 _) _ ->
                    (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ "," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk1 ++ "(True," ++ (term_str t2) ++ "," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> False\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ "eq(" ++ (term_str t3) ++ 
                    "," ++ (term_str t4) ++ ")" ++ (term_str t1) ++ "," ++ 
                    (term_str t2) ++ ")\n" ++
                    fk1 ++ "(True,False," ++ 
                    (term_str t1) ++ "," ++ (term_str t2) ++ ") -> True\n"),
                    (index+2))
                Existl_equation t3 t4 _ ->
                    (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ "," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk1 ++ "(True," ++ (term_str t2) ++ "," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> True\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t3) ++ "," ++
                    (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
                    fk1 ++ "(True," ++ (term_str t4) ++ "," ++ 
                    (term_str t1) ++ "," ++ (term_str t2) ++ ") -> True\n"),
                    (index+2))
                Negation (Existl_equation t3 t4 _) _ ->
                    (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ "," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk1 ++ "(True," ++ (term_str t2) ++ "," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> False\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ "eq(" ++ (term_str t3) ++ 
                    "," ++ (term_str t4) ++ ")" ++ (term_str t1) ++ "," ++ 
                    (term_str t2) ++ ")\n" ++
                    fk1 ++ "(True,False," ++ 
                    (term_str t1) ++ "," ++ (term_str t2) ++ ") -> True\n"),
                    (index+2))
                _ -> error "CASL.CCC.TerminationProof.<impli_str_p_eq_str>"
          Equivalence (Existl_equation t1 t2 _) f2 _ ->
              case (quanti f2) of
                Conjunction _ _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ ")\n" ++
                    fk1 ++ "(True," ++ (term_str t2) ++ ") -> True\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++
                    ") -> " ++ fk2 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (axiom_substr (quanti f2)) ++
                    "," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
                    fk2 ++ "(True,True," ++ (term_str t1) ++ "," ++ 
                    (term_str t2) ++ ") -> True\n"),(index+2))
                Negation (Conjunction _ _) _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ ")\n" ++
                    fk1 ++ "(True," ++ (term_str t2) ++ ") -> False\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++
                    ") -> " ++ fk2 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (axiom_substr (quanti f2)) ++
                    "," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
                    fk2 ++ "(True,False," ++ (term_str t1) ++ "," ++ 
                    (term_str t2) ++ ") -> True\n"),(index+2))
                Disjunction _ _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ ")\n" ++
                    fk1 ++ "(True," ++ (term_str t2) ++ ") -> True\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++
                    ") -> " ++ fk2 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (axiom_substr (quanti f2)) ++
                    "," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
                    fk2 ++ "(True,True," ++ (term_str t1) ++ "," ++ 
                    (term_str t2) ++ ") -> True\n"),(index+2))
                Negation (Disjunction _ _) _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ ")\n" ++
                    fk1 ++ "(True," ++ (term_str t2) ++ ") -> False\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++
                    ") -> " ++ fk2 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (axiom_substr (quanti f2)) ++
                    "," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
                    fk2 ++ "(True,False," ++ (term_str t1) ++ "," ++ 
                    (term_str t2) ++ ") -> True\n"),(index+2))
                Predication predS2 ts2 _ ->
                    (((predSymStr predS2) ++ "(" ++ (terms_str ts2) ++ 
                    ") ->" ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ "," ++
                    (terms_str ts2) ++ ")\n" ++
                    fk1 ++ "(True," ++ (term_str t2) ++ "," ++ 
                    (terms_str ts2) ++ ") -> True\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++
                    ") -> " ++ fk2 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (predSymStr predS2) ++ "(" ++
                    (terms_str ts2) ++ ")," ++ (term_str t1) ++ "," ++
                    (term_str t2) ++ ")\n" ++
                    fk2 ++ "(True,True," ++ (term_str t1) ++ "," ++
                    (term_str t2) ++ ") -> True\n"),(index+2))
                Negation (Predication predS2 ts2 _) _ ->
                    (((predSymStr predS2) ++ "(" ++ (terms_str ts2) ++ 
                    ") ->" ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ "," ++
                    (terms_str ts2) ++ ")\n" ++
                    fk1 ++ "(True," ++ (term_str t2) ++ "," ++ 
                    (terms_str ts2) ++ ") -> False\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++
                    ") -> " ++ fk2 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (predSymStr predS2) ++ "(" ++
                    (terms_str ts2) ++ ")," ++ (term_str t1) ++ "," ++
                    (term_str t2) ++ ")\n" ++
                    fk2 ++ "(True,False," ++ (term_str t1) ++ "," ++
                    (term_str t2) ++ ") -> True\n"),(index+2))
                Strong_equation t3 t4 _ ->
                    (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ "," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk1 ++ "(True," ++ (term_str t2) ++ "," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> True\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t3) ++ "," ++
                    (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
                    fk1 ++ "(True," ++ (term_str t4) ++ "," ++ 
                    (term_str t1) ++ "," ++ (term_str t2) ++ ") -> True\n"),
                    (index+2))
                Negation (Strong_equation t3 t4 _) _ ->
                    (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ "," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk1 ++ "(True," ++ (term_str t2) ++ "," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> False\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ "eq(" ++ (term_str t3) ++ 
                    "," ++ (term_str t4) ++ ")" ++ (term_str t1) ++ "," ++ 
                    (term_str t2) ++ ")\n" ++
                    fk1 ++ "(True,False," ++ 
                    (term_str t1) ++ "," ++ (term_str t2) ++ ") -> True\n"),
                    (index+2))
                Existl_equation t3 t4 _ ->
                    (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ "," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk1 ++ "(True," ++ (term_str t2) ++ "," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> True\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t3) ++ "," ++
                    (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
                    fk1 ++ "(True," ++ (term_str t4) ++ "," ++ 
                    (term_str t1) ++ "," ++ (term_str t2) ++ ") -> True\n"),
                    (index+2))
                Negation (Existl_equation t3 t4 _) _ ->
                    (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ (term_str t1) ++ "," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk1 ++ "(True," ++ (term_str t2) ++ "," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> False\n" ++
                    "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_str ts1) ++ ")," ++ "eq(" ++ (term_str t3) ++ 
                    "," ++ (term_str t4) ++ ")" ++ (term_str t1) ++ "," ++ 
                    (term_str t2) ++ ")\n" ++
                    fk1 ++ "(True,False," ++ 
                    (term_str t1) ++ "," ++ (term_str t2) ++ ") -> True\n"),
                    (index+2))
                _ -> error "CASL.CCC.TerminationProof.<impli_str_p_eq_ex>"
          _ -> error "CASL.CCC.TerminationProof.<impli_str_p>"
    Implication (Strong_equation t1 t2 _) f1 _ _ ->
        case (quanti f1) of
          Conjunction _ _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_str t1) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ") -> True\n"),(index+1))
          Negation (Conjunction _ _) _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_str t1) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ") -> False\n"),(index+1))
          Disjunction _ _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_str t1) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ") -> True\n"),(index+1))
          Negation (Disjunction _ _) _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_str t1) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ") -> False\n"),(index+1))
          Predication predS ts _ ->
              (((predSymStr predS)++"("++(terms_str ts) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1) ++ "," ++ (terms_str ts) ++ 
              ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ "," ++ (terms_str ts) ++
              ") -> True\n"),(index+1))
          Negation (Predication predS ts _) _ ->
              (((predSymStr predS)++"("++(terms_str ts) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1) ++ "," ++ (terms_str ts) ++ 
              ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ "," ++ (terms_str ts) ++
              ") -> False\n"),(index+1))
          Strong_equation t3 t4 _ ->
              (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++ "," ++ 
              (term_str t4) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t3) ++ "," ++
              (term_str t4) ++ ") -> True\n"),(index + 1))
          Negation (Strong_equation t3 t4 _) _ ->
              (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++ "," ++ 
              (term_str t4) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t3) ++ "," ++
              (term_str t4) ++ ") -> False\n"),(index + 1))
          Existl_equation t3 t4 _ ->
              (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++ "," ++ 
              (term_str t4) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t3) ++ "," ++
              (term_str t4) ++ ") -> True\n"),(index + 1))
          Negation (Existl_equation t3 t4 _) _ ->
              (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++ "," ++ 
              (term_str t4) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t3) ++ "," ++
              (term_str t4) ++ ") -> False\n"),(index + 1))
          Equivalence (Predication predS1 ts1 _) f2 _->
              case (quanti f2) of
                Conjunction _ _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ "))\n"++
                    fk1 ++ "(" ++ (term_str t2) ++ ",True) -> True\n"),
                    (index+1))
                Negation (Conjunction _ _) _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ "))\n"++
                    fk1 ++ "(" ++ (term_str t2) ++ ",True) -> False\n"),
                    (index+1))
                Disjunction _ _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ "))\n"++
                    fk1 ++ "(" ++ (term_str t2) ++ ",True) -> True\n"),
                    (index+1))
                Negation (Disjunction _ _) _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ "))\n"++
                    fk1 ++ "(" ++ (term_str t2) ++ ",True) -> False\n"),
                    (index+1))
                Predication predS2 ts2 _ ->
                    (((predSymStr predS2)++"("++(terms_str ts2) ++ ") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ ")," ++
                    (terms_str ts2) ++ ")\n" ++
                    fk1++"("++(term_str t2)++ ",True," ++ (terms_str ts2) ++
                    ") -> True\n"),(index + 1))
                Negation (Predication predS2 ts2 _) _ ->
                    (((predSymStr predS2)++"("++(terms_str ts2) ++ ") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ ")," ++
                    (terms_str ts2) ++ ")\n" ++
                    fk1++"("++(term_str t2)++ ",True," ++ (terms_str ts2) ++
                    ") -> False\n"),(index + 1))
                Strong_equation t3 t4 _ ->
                    (("eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
                    ")," ++ (term_str t3)++","++(term_str t4) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ ",True," ++ 
                    (term_str t3)++ "," ++ (term_str t4) ++ ") -> " ++
                    "True\n"),(index + 1))
                Negation (Strong_equation t3 t4 _) _ ->
                    (("eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
                    ")," ++ (term_str t3)++","++(term_str t4) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ ",True," ++ 
                    (term_str t3)++ "," ++ (term_str t4) ++ ") -> " ++
                    "False\n"),(index + 1))
                Existl_equation t3 t4 _ ->
                    (("eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
                    ")," ++ (term_str t3)++","++(term_str t4) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ ",True," ++ 
                    (term_str t3)++ "," ++ (term_str t4) ++ ") -> " ++
                    "True\n"),(index + 1))
                Negation (Existl_equation t3 t4 _) _ ->
                    (("eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
                    ")," ++ (term_str t3)++","++(term_str t4) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ ",True," ++ 
                    (term_str t3)++ "," ++ (term_str t4) ++ ") -> " ++
                    "False\n"),(index + 1))
                _ -> error "CASL.CCC.TerminationProof.<impli_str_str_eq_p>"
          Equivalence (Strong_equation t3 t4 _) f2 _->
              case (quanti f2) of
                Conjunction _ _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (term_str t3) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ 
                    (term_str t4) ++ ") -> True\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++
                    (axiom_substr (quanti f2)) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",True," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> True\n"),
                    (index+2))
                Negation (Conjunction _ _) _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (term_str t3) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ 
                    (term_str t4) ++ ") -> False\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++
                    (axiom_substr (quanti f2)) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",False," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> True\n"),
                    (index+2))
                Disjunction _ _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (term_str t3) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ 
                    (term_str t4) ++ ") -> True\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++
                    (axiom_substr (quanti f2)) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",True," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> True\n"),
                    (index+2))
                Negation (Disjunction _ _) _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (term_str t3) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ 
                    (term_str t4) ++ ") -> False\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++
                    (axiom_substr (quanti f2)) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",False," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> True\n"),
                    (index+2))
                Predication predS ts _ ->
                    (((predSymStr predS)++"("++(terms_str ts) ++ ") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++ 
                    "," ++ (terms_str ts) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (terms_str ts) ++ ") -> True\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (predSymStr predS) ++ "(" ++ (terms_str ts) ++ ")," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",True," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> True\n"),
                    (index + 2))
                Negation (Predication predS ts _) _ ->
                    (((predSymStr predS)++"("++(terms_str ts) ++ ") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++ 
                    "," ++ (terms_str ts) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (terms_str ts) ++ ") -> False\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (predSymStr predS) ++ "(" ++ (terms_str ts) ++ ")," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",False," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> True\n"),
                    (index + 2))
                Strong_equation t5 t6 _ ->
                    (("eq("++(term_str t5)++","++(term_str t6)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> True\n" ++
                    "eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t5) ++
                    "," ++ (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t6) ++
                    "," ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> True\n"),(index + 2))
                Negation (Strong_equation t5 t6 _) _ ->
                    (("eq("++(term_str t5)++","++(term_str t6)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> False\n" ++
                    "eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ ",eq(" ++ (term_str t5) ++
                    "," ++ (term_str t6) ++ ")," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",False," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> True\n"),(index + 2))
                Existl_equation t5 t6 _ ->
                    (("eq("++(term_str t5)++","++(term_str t6)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> True\n" ++
                    "eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t5) ++
                    "," ++ (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t6) ++
                    "," ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> True\n"),(index + 2))
                Negation (Existl_equation t5 t6 _) _ ->
                    (("eq("++(term_str t5)++","++(term_str t6)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> False\n" ++
                    "eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ ",eq(" ++ (term_str t5) ++
                    "," ++ (term_str t6) ++ ")," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",False," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> True\n"),(index + 2))
                _ -> error "CASL.CCC.TerminationProof.<impli_str_str_eq_str>"
          Equivalence (Existl_equation t3 t4 _) f2 _->
              case (quanti f2) of
                Conjunction _ _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (term_str t3) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ 
                    (term_str t4) ++ ") -> True\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++
                    (axiom_substr (quanti f2)) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",True," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> True\n"),
                    (index+2))
                Negation (Conjunction _ _) _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (term_str t3) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ 
                    (term_str t4) ++ ") -> False\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++
                    (axiom_substr (quanti f2)) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",False," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> True\n"),
                    (index+2))
                Disjunction _ _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (term_str t3) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ 
                    (term_str t4) ++ ") -> True\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++
                    (axiom_substr (quanti f2)) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",True," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> True\n"),
                    (index+2))
                Negation (Disjunction _ _) _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (term_str t3) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ 
                    (term_str t4) ++ ") -> False\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++
                    (axiom_substr (quanti f2)) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",False," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> True\n"),
                    (index+2))
                Predication predS ts _ ->
                    (((predSymStr predS)++"("++(terms_str ts) ++ ") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++ 
                    "," ++ (terms_str ts) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (terms_str ts) ++ ") -> True\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (predSymStr predS) ++ "(" ++ (terms_str ts) ++ ")," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",True," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> True\n"),
                    (index + 2))
                Negation (Predication predS ts _) _ ->
                    (((predSymStr predS)++"("++(terms_str ts) ++ ") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++ 
                    "," ++ (terms_str ts) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (terms_str ts) ++ ") -> False\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (predSymStr predS) ++ "(" ++ (terms_str ts) ++ ")," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",False," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> True\n"),
                    (index + 2))
                Strong_equation t5 t6 _ ->
                    (("eq("++(term_str t5)++","++(term_str t6)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> True\n" ++
                    "eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t5) ++
                    "," ++ (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t6) ++
                    "," ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> True\n"),(index + 2))
                Negation (Strong_equation t5 t6 _) _ ->
                    (("eq("++(term_str t5)++","++(term_str t6)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> False\n" ++
                    "eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ ",eq(" ++ (term_str t5) ++
                    "," ++ (term_str t6) ++ ")," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",False," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> True\n"),(index + 2))
                Existl_equation t5 t6 _ ->
                    (("eq("++(term_str t5)++","++(term_str t6)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> True\n" ++
                    "eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t5) ++
                    "," ++ (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t6) ++
                    "," ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> True\n"),(index + 2))
                Negation (Existl_equation t5 t6 _) _ ->
                    (("eq("++(term_str t5)++","++(term_str t6)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> False\n" ++
                    "eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ ",eq(" ++ (term_str t5) ++
                    "," ++ (term_str t6) ++ ")," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",False," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> True\n"),(index + 2))
                _ -> error "CASL.CCC.TerminationProof.<impli_str_str_eq_ex>"
          _ -> error "CASL.CCC.TerminationProof.<impli_str_str>"
    Implication (Existl_equation t1 t2 _) f1 _ _ ->
        case (quanti f1) of
          Conjunction _ _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_str t1) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ") -> True\n"),(index+1))
          Negation (Conjunction _ _) _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_str t1) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ") -> False\n"),(index+1))
          Disjunction _ _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_str t1) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ") -> True\n"),(index+1))
          Negation (Disjunction _ _) _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_str t1) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ") -> False\n"),(index+1))
          Predication predS ts _ ->
              (((predSymStr predS)++"("++(terms_str ts) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1) ++ "," ++ (terms_str ts) ++ 
              ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ "," ++ (terms_str ts) ++
              ") -> True\n"),(index+1))
          Negation (Predication predS ts _) _ ->
              (((predSymStr predS)++"("++(terms_str ts) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1) ++ "," ++ (terms_str ts) ++ 
              ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ "," ++ (terms_str ts) ++
              ") -> False\n"),(index+1))
          Strong_equation t3 t4 _ ->
              (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++ "," ++ 
              (term_str t4) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t3) ++ "," ++
              (term_str t4) ++ ") -> True\n"),(index + 1))
          Negation (Strong_equation t3 t4 _) _ ->
              (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++ "," ++ 
              (term_str t4) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t3) ++ "," ++
              (term_str t4) ++ ") -> False\n"),(index + 1))
          Existl_equation t3 t4 _ ->
              (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++ "," ++ 
              (term_str t4) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t3) ++ "," ++
              (term_str t4) ++ ") -> True\n"),(index + 1))
          Negation (Existl_equation t3 t4 _) _ ->
              (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++ "," ++ 
              (term_str t4) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t3) ++ "," ++
              (term_str t4) ++ ") -> False\n"),(index + 1))
          Equivalence (Predication predS1 ts1 _) f2 _->
              case (quanti f2) of
                Conjunction _ _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ "))\n"++
                    fk1 ++ "(" ++ (term_str t2) ++ ",True) -> True\n"),
                    (index+1))
                Negation (Conjunction _ _) _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ "))\n"++
                    fk1 ++ "(" ++ (term_str t2) ++ ",True) -> False\n"),
                    (index+1))
                Disjunction _ _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ "))\n"++
                    fk1 ++ "(" ++ (term_str t2) ++ ",True) -> True\n"),
                    (index+1))
                Negation (Disjunction _ _) _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ "))\n"++
                    fk1 ++ "(" ++ (term_str t2) ++ ",True) -> False\n"),
                    (index+1))
                Predication predS2 ts2 _ ->
                    (((predSymStr predS2)++"("++(terms_str ts2) ++ ") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ ")," ++
                    (terms_str ts2) ++ ")\n" ++
                    fk1++"("++(term_str t2)++ ",True," ++ (terms_str ts2) ++
                    ") -> True\n"),(index + 1))
                Negation (Predication predS2 ts2 _) _ ->
                    (((predSymStr predS2)++"("++(terms_str ts2) ++ ") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ ")," ++
                    (terms_str ts2) ++ ")\n" ++
                    fk1++"("++(term_str t2)++ ",True," ++ (terms_str ts2) ++
                    ") -> False\n"),(index + 1))
                Strong_equation t3 t4 _ ->
                    (("eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
                    ")," ++ (term_str t3)++","++(term_str t4) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ ",True," ++ 
                    (term_str t3)++ "," ++ (term_str t4) ++ ") -> " ++
                    "True\n"),(index + 1))
                Negation (Strong_equation t3 t4 _) _ ->
                    (("eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
                    ")," ++ (term_str t3)++","++(term_str t4) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ ",True," ++ 
                    (term_str t3)++ "," ++ (term_str t4) ++ ") -> " ++
                    "False\n"),(index + 1))
                Existl_equation t3 t4 _ ->
                    (("eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
                    ")," ++ (term_str t3)++","++(term_str t4) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ ",True," ++ 
                    (term_str t3)++ "," ++ (term_str t4) ++ ") -> " ++
                    "True\n"),(index + 1))
                Negation (Existl_equation t3 t4 _) _ ->
                    (("eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++
                    (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
                    ")," ++ (term_str t3)++","++(term_str t4) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ ",True," ++ 
                    (term_str t3)++ "," ++ (term_str t4) ++ ") -> " ++
                    "False\n"),(index + 1))
                _ -> error "CASL.CCC.TerminationProof.<impli_str_ex_eq_p>"
          Equivalence (Strong_equation t3 t4 _) f2 _->
              case (quanti f2) of
                Conjunction _ _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (term_str t3) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ 
                    (term_str t4) ++ ") -> True\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++
                    (axiom_substr (quanti f2)) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",True," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> True\n"),
                    (index+2))
                Negation (Conjunction _ _) _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (term_str t3) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ 
                    (term_str t4) ++ ") -> False\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++
                    (axiom_substr (quanti f2)) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",False," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> True\n"),
                    (index+2))
                Disjunction _ _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (term_str t3) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ 
                    (term_str t4) ++ ") -> True\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++
                    (axiom_substr (quanti f2)) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",True," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> True\n"),
                    (index+2))
                Negation (Disjunction _ _) _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (term_str t3) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ 
                    (term_str t4) ++ ") -> False\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++
                    (axiom_substr (quanti f2)) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",False," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> True\n"),
                    (index+2))
                Predication predS ts _ ->
                    (((predSymStr predS)++"("++(terms_str ts) ++ ") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++ 
                    "," ++ (terms_str ts) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (terms_str ts) ++ ") -> True\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (predSymStr predS) ++ "(" ++ (terms_str ts) ++ ")," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",True," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> True\n"),
                    (index + 2))
                Negation (Predication predS ts _) _ ->
                    (((predSymStr predS)++"("++(terms_str ts) ++ ") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++ 
                    "," ++ (terms_str ts) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (terms_str ts) ++ ") -> False\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (predSymStr predS) ++ "(" ++ (terms_str ts) ++ ")," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",False," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> True\n"),
                    (index + 2))
                Strong_equation t5 t6 _ ->
                    (("eq("++(term_str t5)++","++(term_str t6)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> True\n" ++
                    "eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t5) ++
                    "," ++ (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t6) ++
                    "," ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> True\n"),(index + 2))
                Negation (Strong_equation t5 t6 _) _ ->
                    (("eq("++(term_str t5)++","++(term_str t6)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> False\n" ++
                    "eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ ",eq(" ++ (term_str t5) ++
                    "," ++ (term_str t6) ++ ")," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",False," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> True\n"),(index + 2))
                Existl_equation t5 t6 _ ->
                    (("eq("++(term_str t5)++","++(term_str t6)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> True\n" ++
                    "eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t5) ++
                    "," ++ (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t6) ++
                    "," ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> True\n"),(index + 2))
                Negation (Existl_equation t5 t6 _) _ ->
                    (("eq("++(term_str t5)++","++(term_str t6)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> False\n" ++
                    "eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ ",eq(" ++ (term_str t5) ++
                    "," ++ (term_str t6) ++ ")," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",False," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> True\n"),(index + 2))
                _ -> error "CASL.CCC.TerminationProof.<impli_str_ex_eq_str>"
          Equivalence (Existl_equation t3 t4 _) f2 _->
              case (quanti f2) of
                Conjunction _ _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (term_str t3) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ 
                    (term_str t4) ++ ") -> True\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++
                    (axiom_substr (quanti f2)) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",True," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> True\n"),
                    (index+2))
                Negation (Conjunction _ _) _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (term_str t3) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ 
                    (term_str t4) ++ ") -> False\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++
                    (axiom_substr (quanti f2)) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",False," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> True\n"),
                    (index+2))
                Disjunction _ _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (term_str t3) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ 
                    (term_str t4) ++ ") -> True\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++
                    (axiom_substr (quanti f2)) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",True," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> True\n"),
                    (index+2))
                Negation (Disjunction _ _) _ ->
                    (((axiom_substr (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (term_str t3) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ 
                    (term_str t4) ++ ") -> False\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++
                    (axiom_substr (quanti f2)) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",False," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> True\n"),
                    (index+2))
                Predication predS ts _ ->
                    (((predSymStr predS)++"("++(terms_str ts) ++ ") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++ 
                    "," ++ (terms_str ts) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (terms_str ts) ++ ") -> True\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (predSymStr predS) ++ "(" ++ (terms_str ts) ++ ")," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",True," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> True\n"),
                    (index + 2))
                Negation (Predication predS ts _) _ ->
                    (((predSymStr predS)++"("++(terms_str ts) ++ ") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++ 
                    "," ++ (terms_str ts) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (terms_str ts) ++ ") -> False\n" ++
                    "eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++ 
                    (predSymStr predS) ++ "(" ++ (terms_str ts) ++ ")," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",False," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ ") -> True\n"),
                    (index + 2))
                Strong_equation t5 t6 _ ->
                    (("eq("++(term_str t5)++","++(term_str t6)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> True\n" ++
                    "eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t5) ++
                    "," ++ (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t6) ++
                    "," ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> True\n"),(index + 2))
                Negation (Strong_equation t5 t6 _) _ ->
                    (("eq("++(term_str t5)++","++(term_str t6)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> False\n" ++
                    "eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ ",eq(" ++ (term_str t5) ++
                    "," ++ (term_str t6) ++ ")," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",False," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> True\n"),(index + 2))
                Existl_equation t5 t6 _ ->
                    (("eq("++(term_str t5)++","++(term_str t6)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> True\n" ++
                    "eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t5) ++
                    "," ++ (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t6) ++
                    "," ++ (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> True\n"),(index + 2))
                Negation (Existl_equation t5 t6 _) _ ->
                    (("eq("++(term_str t5)++","++(term_str t6)++") -> " ++
                    fk1 ++ "(" ++ (term_str t1) ++ "," ++ (term_str t3) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ ")\n" ++
                    fk1 ++ "(" ++ (term_str t2) ++ "," ++ (term_str t4) ++
                    "," ++ (term_str t5) ++ "," ++ (term_str t6) ++ 
                    ") -> False\n" ++
                    "eq("++(term_str t3)++","++(term_str t4)++") -> " ++
                    fk2 ++ "(" ++ (term_str t1) ++ ",eq(" ++ (term_str t5) ++
                    "," ++ (term_str t6) ++ ")," ++
                    (term_str t3) ++ "," ++ (term_str t4) ++ ")\n" ++
                    fk2 ++ "(" ++ (term_str t2) ++ ",False," ++ 
                    (term_str t3) ++ "," ++ (term_str t4) ++ 
                    ") -> True\n"),(index + 2))
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
                 U1(True,tt_1,...,tt_n) -> t
          --> f(tt_1,...,tt_n)=t => p(t_1,...,t_m)  --> 
                 p(t_1,...,t_m) -> U2(f(tt_1,...,tt_n),t_1,...,t_m)
                 U2(t,t_1,...t_m) -> True 
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
              fk1 ++ "(True) -> True\n"),(index+1))
          Negation (Conjunction _ _) _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
              "))\n" ++
              fk1 ++ "(True) -> False\n"),(index+1))
          Disjunction _ _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
              "))\n" ++
              fk1 ++ "(True) -> True\n"),(index+1))
          Negation (Disjunction _ _) _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
              "))\n" ++
              fk1 ++ "(True) -> False\n"),(index+1))              
          Predication predS2 ts2 _ ->
              (((predSymStr predS2) ++ "(" ++ (terms_str ts2) ++ ") -> " ++
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
              ")," ++ (terms_str ts2) ++ ")\n" ++
              fk1 ++ "(True," ++ (terms_str ts2) ++ ") -> True\n"),
              (index +1))
          Negation (Predication predS2 ts2 _) _ ->           -- !!
              (((predSymStr predS2) ++ "(" ++ (terms_str ts2) ++ ") -> " ++
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++ 
              ")," ++ (terms_str ts2) ++ ")\n" ++
              fk1 ++ "(True," ++ (terms_str ts2) ++ ") -> False\n"),
              (index +1))
          Strong_equation t1 t2 _ -> 
              (("eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
              ")," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk1++"(True,"++(term_str t1)++","++(term_str t2)++") -> " ++
              "True\n"),(index + 1))
          Negation (Strong_equation t1 t2 _) _ ->
              (("eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
              ")," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk1 ++ "(True," ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> False\n"),(index +1))
          Existl_equation t1 t2 _ -> 
              (("eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
              ")," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk1++"(True,"++(term_str t1)++","++(term_str t2)++") -> " ++
              "True\n"),(index + 1))
          Negation (Existl_equation t1 t2 _) _ ->
              (("eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_str ts1) ++
              ")," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk1 ++ "(True," ++ (term_str t1) ++ "," ++ (term_str t2) ++ 
              ") -> False\n"),(index +1))
          _ -> error "CASL.CCC.TerminationProof.<equiv_str_pred>"
    Equivalence (Strong_equation t1 t2 _) f1 _ ->
        case (quanti f1) of
          Conjunction _ _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_str t1) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ") -> True\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk2 ++ "(" ++ (axiom_substr (quanti f1)) ++ "," ++
              (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk2 ++ "(True," ++ (term_str t1) ++ "," ++
              (term_str t2) ++ ") -> True\n"),(index+2))
          Negation (Conjunction _ _) _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_str t1) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ") -> False\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk2 ++ "(" ++ (axiom_substr (quanti f1)) ++ "," ++
              (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk2 ++ "(False," ++ (term_str t1) ++ "," ++
              (term_str t2) ++ ") -> True\n"),(index+2))
          Disjunction _ _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_str t1) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ") -> True\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk2 ++ "(" ++ (axiom_substr (quanti f1)) ++ "," ++
              (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk2 ++ "(True," ++ (term_str t1) ++ "," ++
              (term_str t2) ++ ") -> True\n"),(index+2))
          Negation (Disjunction _ _) _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_str t1) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ") -> False\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk2 ++ "(" ++ (axiom_substr (quanti f1)) ++ "," ++
              (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk2 ++ "(False," ++ (term_str t1) ++ "," ++
              (term_str t2) ++ ") -> True\n"),(index+2))
          Predication predS ts _ ->
              (((predSymStr predS) ++ "(" ++ (terms_str ts) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1) ++ "," ++ (terms_str ts) ++ 
              ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ "," ++ (terms_str ts) ++ 
              ") -> True\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk2 ++ "(" ++ (predSymStr predS) ++ "(" ++ (terms_str ts) ++
              ")," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk2 ++ "(True," ++ (term_str t1) ++ "," ++ (term_str t2) ++
              ") -> True\n"),(index +2))
          Negation (Predication predS ts _) _ ->
              (((predSymStr predS) ++ "(" ++ (terms_str ts) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1) ++ "," ++ (terms_str ts) ++ 
              ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ "," ++ (terms_str ts) ++ 
              ") -> False\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk2 ++ "(" ++ (predSymStr predS) ++ "(" ++ (terms_str ts) ++
              ")," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk2 ++ "(False," ++ (term_str t1) ++ "," ++ (term_str t2) ++
              ") -> True\n"),(index +2))
          Strong_equation t3 t4 _ ->
              (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1)++ "," ++ (term_str t3) ++ 
              "," ++ (term_str t4) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ","++ (term_str t3) ++ 
              "," ++ (term_str t4) ++ ") -> " ++ "True\n" ++ 
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t3)++ "," ++ (term_str t1) ++ 
              "," ++ (term_str t2) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t4) ++ ","++ (term_str t1) ++ 
              "," ++ (term_str t2) ++ ") -> " ++ "True\n"),(index + 2))
          Negation (Strong_equation t3 t4 _) _ ->
              (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1)++ "," ++ (term_str t3) ++ 
              "," ++ (term_str t4) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ","++ (term_str t3) ++ 
              "," ++ (term_str t4) ++ ") -> " ++ "False\n" ++ 
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk1 ++ "(eq(" ++ (term_str t3)++ "," ++ (term_str t4) ++
              ")," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk1 ++ "(False," ++ (term_str t1) ++ 
              "," ++ (term_str t2) ++ ") -> " ++ "True\n"),(index + 2))
          Existl_equation t3 t4 _ ->
              (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1)++ "," ++ (term_str t3) ++ 
              "," ++ (term_str t4) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ","++ (term_str t3) ++ 
              "," ++ (term_str t4) ++ ") -> " ++ "True\n" ++ 
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t3)++ "," ++ (term_str t1) ++ 
              "," ++ (term_str t2) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t4) ++ ","++ (term_str t1) ++ 
              "," ++ (term_str t2) ++ ") -> " ++ "True\n"),(index + 2))
          Negation (Existl_equation t3 t4 _) _ ->
              (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1)++ "," ++ (term_str t3) ++ 
              "," ++ (term_str t4) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ","++ (term_str t3) ++ 
              "," ++ (term_str t4) ++ ") -> " ++ "False\n" ++ 
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk1 ++ "(eq(" ++ (term_str t3)++ "," ++ (term_str t4) ++
              ")," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk1 ++ "(False," ++ (term_str t1) ++ 
              "," ++ (term_str t2) ++ ") -> " ++ "True\n"),(index + 2))
          _ -> error "CASL.CCC.TerminationProof.<equiv_str_str>"
    Equivalence (Existl_equation t1 t2 _) f1 _ ->
        case (quanti f1) of
          Conjunction _ _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_str t1) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ") -> True\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk2 ++ "(" ++ (axiom_substr (quanti f1)) ++ "," ++
              (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk2 ++ "(True," ++ (term_str t1) ++ "," ++
              (term_str t2) ++ ") -> True\n"),(index+2))
          Negation (Conjunction _ _) _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_str t1) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ") -> False\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk2 ++ "(" ++ (axiom_substr (quanti f1)) ++ "," ++
              (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk2 ++ "(False," ++ (term_str t1) ++ "," ++
              (term_str t2) ++ ") -> True\n"),(index+2))
          Disjunction _ _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_str t1) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ") -> True\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk2 ++ "(" ++ (axiom_substr (quanti f1)) ++ "," ++
              (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk2 ++ "(True," ++ (term_str t1) ++ "," ++
              (term_str t2) ++ ") -> True\n"),(index+2))
          Negation (Disjunction _ _) _ ->
              (((axiom_substr (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_str t1) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ") -> False\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk2 ++ "(" ++ (axiom_substr (quanti f1)) ++ "," ++
              (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk2 ++ "(False," ++ (term_str t1) ++ "," ++
              (term_str t2) ++ ") -> True\n"),(index+2))
          Predication predS ts _ ->
              (((predSymStr predS) ++ "(" ++ (terms_str ts) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1) ++ "," ++ (terms_str ts) ++ 
              ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ "," ++ (terms_str ts) ++ 
              ") -> True\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk2 ++ "(" ++ (predSymStr predS) ++ "(" ++ (terms_str ts) ++
              ")," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk2 ++ "(True," ++ (term_str t1) ++ "," ++ (term_str t2) ++
              ") -> True\n"),(index +2))
          Negation (Predication predS ts _) _ ->
              (((predSymStr predS) ++ "(" ++ (terms_str ts) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1) ++ "," ++ (terms_str ts) ++ 
              ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ "," ++ (terms_str ts) ++ 
              ") -> False\n" ++
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk2 ++ "(" ++ (predSymStr predS) ++ "(" ++ (terms_str ts) ++
              ")," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk2 ++ "(False," ++ (term_str t1) ++ "," ++ (term_str t2) ++
              ") -> True\n"),(index +2))
          Strong_equation t3 t4 _ ->
              (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1)++ "," ++ (term_str t3) ++ 
              "," ++ (term_str t4) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ","++ (term_str t3) ++ 
              "," ++ (term_str t4) ++ ") -> " ++ "True\n" ++ 
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t3)++ "," ++ (term_str t1) ++ 
              "," ++ (term_str t2) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t4) ++ ","++ (term_str t1) ++ 
              "," ++ (term_str t2) ++ ") -> " ++ "True\n"),(index + 2))
          Negation (Strong_equation t3 t4 _) _ ->
              (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1)++ "," ++ (term_str t3) ++ 
              "," ++ (term_str t4) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ","++ (term_str t3) ++ 
              "," ++ (term_str t4) ++ ") -> " ++ "False\n" ++ 
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk1 ++ "(eq(" ++ (term_str t3)++ "," ++ (term_str t4) ++
              ")," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk1 ++ "(False," ++ (term_str t1) ++ 
              "," ++ (term_str t2) ++ ") -> " ++ "True\n"),(index + 2))
          Existl_equation t3 t4 _ ->
              (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1)++ "," ++ (term_str t3) ++ 
              "," ++ (term_str t4) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ","++ (term_str t3) ++ 
              "," ++ (term_str t4) ++ ") -> " ++ "True\n" ++ 
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t3)++ "," ++ (term_str t1) ++ 
              "," ++ (term_str t2) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t4) ++ ","++ (term_str t1) ++ 
              "," ++ (term_str t2) ++ ") -> " ++ "True\n"),(index + 2))
          Negation (Existl_equation t3 t4 _) _ ->
              (("eq(" ++ (term_str t3) ++ "," ++ (term_str t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_str t1)++ "," ++ (term_str t3) ++ 
              "," ++ (term_str t4) ++ ")\n" ++
              fk1 ++ "(" ++ (term_str t2) ++ ","++ (term_str t3) ++ 
              "," ++ (term_str t4) ++ ") -> " ++ "False\n" ++ 
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> " ++
              fk1 ++ "(eq(" ++ (term_str t3)++ "," ++ (term_str t4) ++
              ")," ++ (term_str t1) ++ "," ++ (term_str t2) ++ ")\n" ++
              fk1 ++ "(False," ++ (term_str t1) ++ 
              "," ++ (term_str t2) ++ ") -> " ++ "True\n"),(index + 2))
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
        conj_str fs ++ " -> True"
    Disjunction fs _ -> 
        disj_str fs ++ " -> True"
    Negation f' _ ->
        case f' of
          Conjunction fs _ ->
              conj_str fs ++ " -> False"
          Disjunction fs _ ->
              disj_str fs ++ " -> False"
          Predication p_s ts _ -> 
              ((predSymStr p_s) ++ "(" ++ (terms_str ts) ++ ") -> False")
          Existl_equation t1 t2 _ -> 
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> False"
          Strong_equation t1 t2 _ -> 
              "eq(" ++ (term_str t1) ++ "," ++ (term_str t2) ++ ") -> False"
          Definedness _ _ -> ""           -- not implement
          _ -> error "CASL.CCC.TerminationProof.<Axioms_Negation>"
    True_atom _ -> 
        error "CASL.CCC.TerminationProof.<Axioms_True>"     
    False_atom _ -> 
        error "CASL.CCC.TerminationProof.<Axioms_False>"
    Predication p_s ts _ -> 
        ((predSymStr p_s) ++ "(" ++ (terms_str ts) ++ ") -> True")
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
        "True"     
    False_atom _ -> 
        "False"
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


-- the signature for auxiliary function
   -- input axiom
   -- functionindex
   -- functionname
   -- number of arguments
   -- next functionindex
sigAuxf :: FORMULA f -> Int -> [((String,Int),Int)]
sigAuxf f i = 
        case (quanti f) of
          Implication _ f' _ _ -> 
              case (quanti f') of
                Conjunction _ _ ->
                    [((("af"++show(i)),1),i+1)]
                Negation (Conjunction _ _) _ ->
                    [((("af"++show(i)),1),i+1)]
                Disjunction _ _ ->
                    [((("af"++show(i)),1),i+1)]
                Negation (Disjunction _ _) _ ->
                    [((("af"++show(i)),1),i+1)]
                Predication _ ts _ ->
                    [((("af"++show(i)),1+(length ts)),i+1)]
                Negation (Predication _ ts _) _ ->
                    [((("af"++show(i)),1+(length ts)),i+1)]
                Strong_equation _ _ _ ->
                    [((("af"++show(i)),3),i+1)]
                Negation (Strong_equation _ _ _) _ -> 
                    [((("af"++show(i)),3),i+1)]
                Existl_equation _ _ _ ->
                    [((("af"++show(i)),3),i+1)]
                Negation (Existl_equation _ _ _) _ -> 
                    [((("af"++show(i)),3),i+1)] 
                Equivalence (Predication _ _ _) f1 _  ->
                    case (quanti f1) of
                      Conjunction _ _ ->
                          [((("af"++show(i)),2),i+1)]
                      Negation (Conjunction _ _) _ ->
                          [((("af"++show(i)),2),i+1)]
                      Disjunction _ _ ->
                          [((("af"++show(i)),2),i+1)]
                      Negation (Disjunction _ _) _ ->
                          [((("af"++show(i)),2),i+1)]
                      Predication _ ts _ -> 
                          [((("af"++show(i)),2+(length ts)),i+1)]
                      Negation (Predication _ ts _) _ ->
                          [((("af"++show(i)),2+(length ts)),i+1)]
                      Strong_equation _ _ _ ->
                          [((("af"++show(i)),4),i+1)]
                      Negation (Strong_equation _ _ _) _ ->
                          [((("af"++show(i)),4),i+1)]
                      Existl_equation _ _ _ ->
                          [((("af"++show(i)),4),i+1)]
                      Negation (Existl_equation _ _ _) _ ->
                          [((("af"++show(i)),4),i+1)]
                      _ -> [(("",-1),i)]
                Equivalence (Strong_equation _ _ _) f1 _  ->
                    case (quanti f1) of
                      Conjunction _ _ ->
                          [((("af"++show(i)),2),i+2),
                           ((("af"++show(i+1)),4),i+2)]
                      Negation (Conjunction _ _) _ ->
                          [((("af"++show(i)),2),i+2),
                           ((("af"++show(i+1)),4),i+2)]
                      Disjunction _ _ ->
                          [((("af"++show(i)),2),i+2),
                           ((("af"++show(i+1)),4),i+2)]
                      Negation (Disjunction _ _) _ ->
                          [((("af"++show(i)),2),i+2),
                           ((("af"++show(i+1)),4),i+2)]
                      Predication _ ts _ -> 
                          [((("af"++show(i)),2+(length ts)),i+2),
                           ((("af"++show(i+1)),4),i+2)]
                      Negation (Predication _ ts _) _ ->
                          [((("af"++show(i)),2+(length ts)),i+2),
                           ((("af"++show(i+1)),4),i+2)]
                      Strong_equation _ _ _ ->
                          [((("af"++show(i)),4),i+2),
                           ((("af"++show(i+1)),4),i+2)]
                      Negation (Strong_equation _ _ _) _ ->
                          [((("af"++show(i)),4),i+2),
                           ((("af"++show(i+1)),4),i+2)]
                      Existl_equation _ _ _ ->
                          [((("af"++show(i)),4),i+2),
                           ((("af"++show(i+1)),4),i+2)]
                      Negation (Existl_equation _ _ _) _ ->
                          [((("af"++show(i)),4),i+2),
                           ((("af"++show(i+1)),4),i+2)]
                      _ -> [(("",-1),i)]
                Equivalence (Existl_equation _ _ _) f1 _  ->
                    case (quanti f1) of
                      Conjunction _ _ ->
                          [((("af"++show(i)),2),i+2),
                           ((("af"++show(i+1)),4),i+2)]
                      Negation (Conjunction _ _) _ ->
                          [((("af"++show(i)),2),i+2),
                           ((("af"++show(i+1)),4),i+2)]
                      Disjunction _ _ ->
                          [((("af"++show(i)),2),i+2),
                           ((("af"++show(i+1)),4),i+2)]
                      Negation (Disjunction _ _) _ ->
                          [((("af"++show(i)),2),i+2),
                           ((("af"++show(i+1)),4),i+2)]
                      Predication _ ts _ -> 
                          [((("af"++show(i)),2+(length ts)),i+2),
                           ((("af"++show(i+1)),4),i+2)]
                      Negation (Predication _ ts _) _ ->
                          [((("af"++show(i)),2+(length ts)),i+2),
                           ((("af"++show(i+1)),4),i+2)]
                      Strong_equation _ _ _ ->
                          [((("af"++show(i)),4),i+2),
                           ((("af"++show(i+1)),4),i+2)]
                      Negation (Strong_equation _ _ _) _ ->
                          [((("af"++show(i)),4),i+2),
                           ((("af"++show(i+1)),4),i+2)]
                      Existl_equation _ _ _ ->
                          [((("af"++show(i)),4),i+2),
                           ((("af"++show(i+1)),4),i+2)]
                      Negation (Existl_equation _ _ _) _ ->
                          [((("af"++show(i)),4),i+2),
                           ((("af"++show(i+1)),4),i+2)]
                      _ -> [(("",-1),i)]
                _ -> [(("",-1),i)]
          Equivalence (Predication _ _ _) f' _ ->
              case (quanti f') of
                Conjunction _ _ ->
                    [((("af"++show(i)),1),i+1)]
                Negation (Conjunction _ _) _ ->
                    [((("af"++show(i)),1),i+1)]
                Disjunction _ _ ->
                    [((("af"++show(i)),1),i+1)]
                Negation (Disjunction _ _) _ ->
                    [((("af"++show(i)),1),i+1)]
                Predication _ ts _ ->
                    [((("af"++show(i)),1+(length ts)),i+1)]
                Negation (Predication _ ts _) _ ->
                    [((("af"++show(i)),1+(length ts)),i+1)]
                Strong_equation _ _ _ ->
                    [((("af"++show(i)),3),i+1)]
                Negation (Strong_equation _ _ _) _ ->
                    [((("af"++show(i)),3),i+1)]
                Existl_equation _ _ _ ->
                    [((("af"++show(i)),3),i+1)]
                Negation (Existl_equation _ _ _) _ ->
                    [((("af"++show(i)),3),i+1)]
                _ -> [(("",-1),i)]
          Equivalence (Strong_equation _ _ _) f' _ ->
              case (quanti f') of
                Conjunction _ _ ->
                    [((("af"++show(i)),1),i+2),
                     ((("af"++show(i+1)),3),i+2)]
                Negation (Conjunction _ _) _ ->
                    [((("af"++show(i)),1),i+2),
                     ((("af"++show(i+1)),3),i+2)]
                Disjunction _ _ ->
                    [((("af"++show(i)),1),i+2),
                     ((("af"++show(i+1)),3),i+2)]
                Negation (Disjunction _ _) _ ->
                    [((("af"++show(i)),1),i+2),
                     ((("af"++show(i+1)),3),i+2)]
                Predication _ ts _ ->
                    [((("af"++show(i)),1+(length ts)),i+2),
                     ((("af"++show(i+1)),3),i+2)]
                Negation (Predication _ ts _) _ ->
                    [((("af"++show(i)),1+(length ts)),i+2),
                     ((("af"++show(i+1)),3),i+2)]
                Strong_equation _ _ _ ->
                    [((("af"++show(i)),3),i+2),
                     ((("af"++show(i+1)),3),i+2)]
                Negation (Strong_equation _ _ _) _ ->
                    [((("af"++show(i)),3),i+2),
                     ((("af"++show(i+1)),3),i+2)]
                Existl_equation _ _ _ ->
                    [((("af"++show(i)),3),i+2),
                     ((("af"++show(i+1)),3),i+2)]
                Negation (Existl_equation _ _ _) _ ->
                    [((("af"++show(i)),3),i+2),
                     ((("af"++show(i+1)),3),i+2)]
                _ -> [(("",-1),i)]
          Equivalence (Existl_equation _ _ _) f' _ ->
              case (quanti f') of
                Conjunction _ _ ->
                    [((("af"++show(i)),1),i+2),
                     ((("af"++show(i+1)),3),i+2)]
                Negation (Conjunction _ _) _ ->
                    [((("af"++show(i)),1),i+2),
                     ((("af"++show(i+1)),3),i+2)]
                Disjunction _ _ ->
                    [((("af"++show(i)),1),i+2),
                     ((("af"++show(i+1)),3),i+2)]
                Negation (Disjunction _ _) _ ->
                    [((("af"++show(i)),1),i+2),
                     ((("af"++show(i+1)),3),i+2)]
                Predication _ ts _ ->
                    [((("af"++show(i)),1+(length ts)),i+2),
                     ((("af"++show(i+1)),3),i+2)]
                Negation (Predication _ ts _) _ ->
                    [((("af"++show(i)),1+(length ts)),i+2),
                     ((("af"++show(i+1)),3),i+2)]
                Strong_equation _ _ _ ->
                    [((("af"++show(i)),3),i+2),
                     ((("af"++show(i+1)),3),i+2)]
                Negation (Strong_equation _ _ _) _ ->
                    [((("af"++show(i)),3),i+2),
                     ((("af"++show(i+1)),3),i+2)]
                Existl_equation _ _ _ ->
                    [((("af"++show(i)),3),i+2),
                     ((("af"++show(i+1)),3),i+2)]
                Negation (Existl_equation _ _ _) _ ->
                    [((("af"++show(i)),3),i+2),
                     ((("af"++show(i+1)),3),i+2)]
                _ -> [(("",-1),i)]
          _ -> [(("",-1),i)]     


terms_str :: [TERM f] -> String
terms_str ts = 
    if null ts then ""
    else tail $ concat $ map (\s->","++s) $ map term_str ts



