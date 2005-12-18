{- | 

    Module      :  $Header$
    Copyright   :  (c) Mingyi Liu and Till Mossakowski and Uni Bremen 2004-2005
    License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

    Maintainer  :  hets@tzi.de
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
   using cime, see http://cime.lri.fr/

  interface to cime system, using system
  transform CASL signature to Cime signature, 
  CASL formulas to Cime rewrite rules
-}

terminationProof :: (PosItem f, PrettyPrint f, Eq f) => 
                    [Named (FORMULA f)] -> Bool
terminationProof fsn = (not $ null all_axioms) && (not $ proof)
    where
    fs1 = map sentence (filter is_user_or_sort_gen fsn)
    fs = trace (showPretty fs1 "all formulars") fs1
    all_axioms1 = filter (\f->(not $ is_Sort_gen_ax f) &&
                              (not $ is_Membership f) &&
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
                                              (opS_cime $ head signs) ++ ";\n")
    --  build signature of predication together 
    predSignStr signs str                      
        | null signs = str
        | otherwise = 
            predSignStr (tail signs) (str ++ 
                                      (predS_cime $ head signs) ++ ";\n")
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
            axiomStr (tail axs) (str ++ (axiom_cime $ (head axs)) ++ ";\n")
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
            where tmp = impli_equiv_cime i (head afs)
    axAux = auxAxstr impli_equiv 1 ""  
    varhead = "let X = vars \"t1 t2 "
    axhead = "let axioms = TRS F X \"eq(t1,t1) -> True;\n" ++ 
                                    "eq(t1,t2) -> False;\n" ++
                                    "and(True,True) -> True;\n" ++
                                    "and(True,False) -> False;\n" ++
                                    "and(False,True) -> False;\n" ++
                                    "and(False,False) -> False;\n" ++
                                    "or(True,True) -> True;\n" ++
                                    "or(True,False) -> True;\n" ++
                                    "or(False,True) -> True;\n" ++
                                    "or(False,False) -> False;\n" ++
                                    "not(True) -> False;\n" ++
                                    "not(False) -> True;\n" ++  
                                    "when_else(t1,True,t2) -> t1;\n" ++ 
                                    "when_else(t1,False,t2) -> t2;\n"
    c_sigs = (sighead ++ (opSignStr (everyOnce (constructors ++
                                                op_Syms)) "") ++
                         (predSignStr all_predSymbs "") ++
              sigAux ++ "\";\n")
    c_vars = (varhead ++ (varsStr (allVar $ map varOfAxiom $ 
                                   all_axioms) "") ++ "\"; \n")
    c_axms = if null n_impli_equiv 
             then (axhead ++ axAux ++ "\";\n")
             else (axhead ++ (axiomStr n_impli_equiv "") ++ axAux ++ "\";\n")
    ipath = "/tmp/Input.cime"
    opath = "/tmp/Result.cime"
    c_proof = ("termcrit \"dp\";\n" ++
               "termination axioms;\n" ++
               "#quit;")  
    proof = unsafePerformIO (do
                writeFile ipath (c_sigs ++ c_vars ++ c_axms ++ c_proof)
                system ("cime < " ++ ipath ++ " | cat > " ++ opath)
                res <- readFile opath
                -- system ("rm ./CASL/CCC/*.cime")
                return (subStr "Termination proof found." res))


type Cime = String


{- transform Id to cime
   because cime these symbols '[' and ']' do not know, 
   these symbols are replaced by '|'       (idStrT)
-}
id_cime :: Id -> Cime 
id_cime _id = map (\s-> case s of
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


{- transform a term to cime (termStr)
-}
term_cime :: TERM f -> Cime
term_cime t = 
  case (term t) of
    Qual_var var _ _ -> tokStr var
    Application (Op_name opn) _ _ ->
        id_cime opn
    Application (Qual_op_name opn _ _) ts _ -> 
        if null ts then (id_cime opn)
        else ((id_cime opn) ++ "(" ++ 
             (tail $ concat $ map (\s->","++s) $ map term_cime ts)++")")
    Conditional t1 f t2 _ -> 
        ("when_else("++(term_cime t1)++","++
         (t_f_str f)++","++(term_cime t2)++")")  
    _ -> error "CASL.CCC.TerminationProof.<Term>"
  where t_f_str f=case f of                     --  condition of term
                    Strong_equation t1 t2 _ -> 
                        ("eq("++(term_cime t1)++","++(term_cime t2)++")")
               --    Predication PRED_SYMB [TERM f] Range
                    Predication ps ts _ ->
                        ((predSymStr ps) ++ "(" ++
                        (terms_cime ts) ++ ")")
                    _ -> error "CASL.CCC.TerminationProof.<Term-Formula>"


dimension :: Int -> String
dimension a = case a of
                0 -> " : constant"
                1 -> " : unary"
                2 -> " : binary"
                _ -> " : " ++ (show a)


{- transform OP_SYMB to Signature of cime (opStr)
-}
opS_cime :: OP_SYMB -> Cime
opS_cime o_s = 
  case o_s of
    Qual_op_name op_n (Op_type _ a_sorts _ _) _ -> 
        ((id_cime op_n) ++ (dimension $ length a_sorts))
    _ -> error "CASL.CCC.TerminationProof.<Signature_OP_SYMB: Op_name>"


{- transform PRED_SYMB to Signature of cime (predStr)
-}
predS_cime :: PRED_SYMB -> Cime
predS_cime p_s = 
  case p_s of
    Qual_pred_name pred_n (Pred_type sts _) _ -> 
        ((id_cime pred_n) ++ (dimension $ length sts))
    _ -> error "CASL.CCC.TerminationProof.<predS_cime>"


{- transform Implication to cime:
   i: (phi => f(t_1,...,t_m)=t)
     Example: 
                X=e => f(t_1,...,t_m)=t
     cime -->   f(t_1,...,t_m) -> U(X,t_1,...,t_m);
                U(e,t_1,...t_m) -> t;
   P.S. Bool ignore

   ii: (phi1  => p(t_1,...,t_m)<=>phi)
     Example:
            X=e => p(t_1,...,t_m) <=> f(tt_1,...,tt_n)=t
     cime --> X=e =>  p(t_1,...,t_m)  => f(tt_1,...,tt_n)=t  --> 
                  f(tt_1,...,tt_n) -> U1(X,p(t_1,...,t_m),tt_1,...,tt_n);
                  U1(e,True,tt_1,...,tt_n) -> t;
          --> X=e =>  f(tt_1,...,tt_n)=t => p(t_1,...,t_m)   --> 
                  p(t_1,...,t_m) -> U2(X,f(tt_1,...,tt_n),t_1,...,t_m);
                  U2(e,t,t_1,...,t_m) -> True; 
-}
impli_cime :: Int -> FORMULA f -> (Cime,Int)
impli_cime index f =
  case (quanti f) of
    Implication (Predication predS1 ts1 _) f1 _ _ ->
        case (quanti f1) of
          Conjunction _ _ ->
              (((axiom_subcime (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++ 
              "));\n" ++
              fk1 ++ "(True) -> True;\n"),(index+1))
          Negation (Conjunction _ _) _ ->
              (((axiom_subcime (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++ 
              "));\n" ++
              fk1 ++ "(True) -> False;\n"),(index+1))
          Disjunction _ _ ->
              (((axiom_subcime (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++ 
              "));\n" ++
              fk1 ++ "(True) -> True;\n"),(index+1))
          Negation (Disjunction _ _) _ ->
              (((axiom_subcime (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++ 
              "));\n" ++
              fk1 ++ "(True) -> False;\n"),(index+1))
          Predication predS2 ts2 _ ->
              (((predSymStr predS2) ++ "(" ++ (terms_cime ts2) ++ ") -> " ++
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++
              ")," ++ (terms_cime ts2) ++ ");\n" ++
              fk1 ++ "(True," ++ (terms_cime ts2) ++ ") -> True;\n" ),
              (index+1))
          Negation (Predication predS2 ts2 _) _ ->
              (((predSymStr predS2) ++ "(" ++ (terms_cime ts2) ++ ") -> " ++
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++
              ")," ++ (terms_cime ts2) ++ ");\n" ++
              fk1 ++ "(True," ++ (terms_cime ts2) ++ ") -> False;\n" ),
              (index+1))
          Strong_equation t1 t2 _ ->
              (("eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ") -> " ++
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++
              ")," ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ");\n" ++
              fk1 ++ "(True," ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ 
              ") -> True;\n"),(index + 1))
          Negation (Strong_equation t1 t2 _) _ ->
              (("eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ") -> " ++
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++
              ")," ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ");\n" ++
              fk1 ++ "(True," ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ 
              ") -> False;\n"),(index + 1))
          Existl_equation t1 t2 _ ->
              (("eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ") -> " ++
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++
              ")," ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ");\n" ++
              fk1 ++ "(True," ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ 
              ") -> True;\n"),(index + 1))
          Negation (Existl_equation t1 t2 _) _ ->
              (("eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ") -> " ++
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++
              ")," ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ");\n" ++
              fk1 ++ "(True," ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ 
              ") -> False;\n"),(index + 1))
          Equivalence (Predication predS2 ts2 _) f2 _ ->
              case (quanti f2) of
                Conjunction _ _ ->
                    (((axiom_subcime (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (predSymStr predS2) ++ "(" ++ 
                    (terms_cime ts2) ++"));\n" ++
                    fk1 ++ "(True,True) -> True;\n"),(index+1))
                Negation (Conjunction _ _) _ ->
                    (((axiom_subcime (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (predSymStr predS2) ++ "(" ++ 
                    (terms_cime ts2) ++"));\n" ++
                    fk1 ++ "(True,True) -> False;\n"),(index+1))
                Disjunction _ _ ->
                    (((axiom_subcime (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (predSymStr predS2) ++ "(" ++ 
                    (terms_cime ts2) ++"));\n" ++
                    fk1 ++ "(True,True) -> True;\n"),(index+1))
                Negation (Disjunction _ _) _ ->
                    (((axiom_subcime (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (predSymStr predS2) ++ "(" ++ 
                    (terms_cime ts2) ++"));\n" ++
                    fk1 ++ "(True,True) -> False;\n"),(index+1))
                Predication predS3 ts3 _ ->
                    (((predSymStr predS3)++"("++(terms_cime ts3)++") -> "++
                    fk1++"("++(predSymStr predS1)++"("++(terms_cime ts1) ++ 
                    ")," ++ (predSymStr predS2) ++ "(" ++ (terms_cime ts2) ++
                    ")," ++ (terms_cime ts3) ++ ");\n" ++
                    fk1++"(True,True,"++(terms_cime ts3)++") -> True;\n"),
                    (index +1))
                Negation (Predication predS3 ts3 _) _ ->
                    (((predSymStr predS3)++"("++(terms_cime ts3)++") -> "++
                    fk1++"("++(predSymStr predS1)++"("++(terms_cime ts1) ++ 
                    ")," ++ (predSymStr predS2) ++ "(" ++ (terms_cime ts2) ++
                    ")," ++ (terms_cime ts3) ++ ");\n" ++
                    fk1++"(True,True,"++(terms_cime ts3)++") -> False;\n"),
                    (index + 1))
                Strong_equation t1 t2 _ ->
                    (("eq("++(term_cime t1)++","++(term_cime t2)++") -> " ++
                    fk1++"("++(predSymStr predS1)++"("++(terms_cime ts1)++
                    ")," ++ (predSymStr predS2) ++ "(" ++ (terms_cime ts2) ++
                    "),"++(term_cime t1)++","++(term_cime t2)++");\n" ++
                    fk1++"(True,True,"++(term_cime t1)++","++(term_cime t2)++ 
                    ") -> True;\n"),(index +1))
                Negation (Strong_equation t1 t2 _) _ ->
                    (("eq("++(term_cime t1)++","++(term_cime t2)++") -> " ++
                    fk1++"("++(predSymStr predS1)++"("++(terms_cime ts1)++
                    ")," ++ (predSymStr predS2) ++ "(" ++ (terms_cime ts2) ++
                    "),"++(term_cime t1)++","++(term_cime t2)++");\n" ++
                    fk1++"(True,True,"++(term_cime t1)++","++(term_cime t2)++ 
                    ") -> False;\n"),(index +1))
                Existl_equation t1 t2 _ ->
                    (("eq("++(term_cime t1)++","++(term_cime t2)++") -> " ++
                    fk1++"("++(predSymStr predS1)++"("++(terms_cime ts1)++
                    ")," ++ (predSymStr predS2) ++ "(" ++ (terms_cime ts2) ++
                    "),"++(term_cime t1)++","++(term_cime t2)++");\n" ++
                    fk1++"(True,True,"++(term_cime t1)++","++(term_cime t2)++ 
                    ") -> True;\n"),(index +1))
                Negation (Existl_equation t1 t2 _) _ ->
                    (("eq("++(term_cime t1)++","++(term_cime t2)++") -> " ++
                    fk1++"("++(predSymStr predS1)++"("++(terms_cime ts1)++
                    ")," ++ (predSymStr predS2) ++ "(" ++ (terms_cime ts2) ++
                    "),"++(term_cime t1)++","++(term_cime t2)++");\n" ++
                    fk1++"(True,True,"++(term_cime t1)++","++(term_cime t2)++ 
                    ") -> False;\n"),(index +1))
                _ -> error "CASL.CCC.TerminationProof.<impli_cime_p_eq_p>"
          Equivalence (Strong_equation t1 t2 _) f2 _ ->
              case (quanti f2) of
                Conjunction _ _ ->
                    (((axiom_subcime (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (term_cime t1) ++ ");\n" ++
                    fk1 ++ "(True," ++ (term_cime t2) ++ ") -> True;\n" ++
                    "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++
                    ") -> " ++ fk2 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (axiom_subcime (quanti f2)) ++
                    "," ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ");\n" ++
                    fk2 ++ "(True,True," ++ (term_cime t1) ++ "," ++ 
                    (term_cime t2) ++ ") -> True;\n"),(index+2))
                Negation (Conjunction _ _) _ ->
                    (((axiom_subcime (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (term_cime t1) ++ ");\n" ++
                    fk1 ++ "(True," ++ (term_cime t2) ++ ") -> False;\n" ++
                    "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++
                    ") -> " ++ fk2 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (axiom_subcime (quanti f2)) ++
                    "," ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ");\n" ++
                    fk2 ++ "(True,False," ++ (term_cime t1) ++ "," ++ 
                    (term_cime t2) ++ ") -> True;\n"),(index+2))
                Disjunction _ _ ->
                    (((axiom_subcime (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (term_cime t1) ++ ");\n" ++
                    fk1 ++ "(True," ++ (term_cime t2) ++ ") -> True;\n" ++
                    "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++
                    ") -> " ++ fk2 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (axiom_subcime (quanti f2)) ++
                    "," ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ");\n" ++
                    fk2 ++ "(True,True," ++ (term_cime t1) ++ "," ++ 
                    (term_cime t2) ++ ") -> True;\n"),(index+2))
                Negation (Disjunction _ _) _ ->
                    (((axiom_subcime (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (term_cime t1) ++ ");\n" ++
                    fk1 ++ "(True," ++ (term_cime t2) ++ ") -> False;\n" ++
                    "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++
                    ") -> " ++ fk2 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (axiom_subcime (quanti f2)) ++
                    "," ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ");\n" ++
                    fk2 ++ "(True,False," ++ (term_cime t1) ++ "," ++ 
                    (term_cime t2) ++ ") -> True;\n"),(index+2))
                Predication predS2 ts2 _ ->
                    (((predSymStr predS2) ++ "(" ++ (terms_cime ts2) ++ 
                    ") ->" ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (term_cime t1) ++ "," ++
                    (terms_cime ts2) ++ ");\n" ++
                    fk1 ++ "(True," ++ (term_cime t2) ++ "," ++ 
                    (terms_cime ts2) ++ ") -> True;\n" ++
                    "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++
                    ") -> " ++ fk2 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (predSymStr predS2) ++ "(" ++
                    (terms_cime ts2) ++ ")," ++ (term_cime t1) ++ "," ++
                    (term_cime t2) ++ ");\n" ++
                    fk2 ++ "(True,True," ++ (term_cime t1) ++ "," ++
                    (term_cime t2) ++ ") -> True;\n"),(index+2))
                Negation (Predication predS2 ts2 _) _ ->
                    (((predSymStr predS2) ++ "(" ++ (terms_cime ts2) ++ 
                    ") ->" ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (term_cime t1) ++ "," ++
                    (terms_cime ts2) ++ ");\n" ++
                    fk1 ++ "(True," ++ (term_cime t2) ++ "," ++ 
                    (terms_cime ts2) ++ ") -> False;\n" ++
                    "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++
                    ") -> " ++ fk2 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (predSymStr predS2) ++ "(" ++
                    (terms_cime ts2) ++ ")," ++ (term_cime t1) ++ "," ++
                    (term_cime t2) ++ ");\n" ++
                    fk2 ++ "(True,False," ++ (term_cime t1) ++ "," ++
                    (term_cime t2) ++ ") -> True;\n"),(index+2))
                Strong_equation t3 t4 _ ->
                    (("eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (term_cime t1) ++ "," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ");\n" ++
                    fk1 ++ "(True," ++ (term_cime t2) ++ "," ++ 
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> True;\n" ++
                    "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (term_cime t3) ++ "," ++
                    (term_cime t1) ++ "," ++ (term_cime t2) ++ ");\n" ++
                    fk1 ++ "(True," ++ (term_cime t4) ++ "," ++ 
                    (term_cime t1) ++ "," ++ (term_cime t2) ++ ") -> True;\n"),
                    (index+2))
                Negation (Strong_equation t3 t4 _) _ ->
                    (("eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (term_cime t1) ++ "," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ");\n" ++
                    fk1 ++ "(True," ++ (term_cime t2) ++ "," ++ 
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> False;\n" ++
                    "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ "eq(" ++ (term_cime t3) ++ 
                    "," ++ (term_cime t4) ++ ")" ++ (term_cime t1) ++ "," ++ 
                    (term_cime t2) ++ ");\n" ++
                    fk1 ++ "(True,False," ++ 
                    (term_cime t1) ++ "," ++ (term_cime t2) ++ ") -> True;\n"),
                    (index+2))
                Existl_equation t3 t4 _ ->
                    (("eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (term_cime t1) ++ "," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ");\n" ++
                    fk1 ++ "(True," ++ (term_cime t2) ++ "," ++ 
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> True;\n" ++
                    "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (term_cime t3) ++ "," ++
                    (term_cime t1) ++ "," ++ (term_cime t2) ++ ");\n" ++
                    fk1 ++ "(True," ++ (term_cime t4) ++ "," ++ 
                    (term_cime t1) ++ "," ++ (term_cime t2) ++ ") -> True;\n"),
                    (index+2))
                Negation (Existl_equation t3 t4 _) _ ->
                    (("eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (term_cime t1) ++ "," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ");\n" ++
                    fk1 ++ "(True," ++ (term_cime t2) ++ "," ++ 
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> False;\n" ++
                    "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ "eq(" ++ (term_cime t3) ++ 
                    "," ++ (term_cime t4) ++ ")" ++ (term_cime t1) ++ "," ++ 
                    (term_cime t2) ++ ");\n" ++
                    fk1 ++ "(True,False," ++ 
                    (term_cime t1) ++ "," ++ (term_cime t2) ++ ") -> True;\n"),
                    (index+2))
                _ -> error "CASL.CCC.TerminationProof.<impli_cime_p_eq_str>"
          Equivalence (Existl_equation t1 t2 _) f2 _ ->
              case (quanti f2) of
                Conjunction _ _ ->
                    (((axiom_subcime (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (term_cime t1) ++ ");\n" ++
                    fk1 ++ "(True," ++ (term_cime t2) ++ ") -> True;\n" ++
                    "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++
                    ") -> " ++ fk2 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (axiom_subcime (quanti f2)) ++
                    "," ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ");\n" ++
                    fk2 ++ "(True,True," ++ (term_cime t1) ++ "," ++ 
                    (term_cime t2) ++ ") -> True;\n"),(index+2))
                Negation (Conjunction _ _) _ ->
                    (((axiom_subcime (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (term_cime t1) ++ ");\n" ++
                    fk1 ++ "(True," ++ (term_cime t2) ++ ") -> False;\n" ++
                    "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++
                    ") -> " ++ fk2 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (axiom_subcime (quanti f2)) ++
                    "," ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ");\n" ++
                    fk2 ++ "(True,False," ++ (term_cime t1) ++ "," ++ 
                    (term_cime t2) ++ ") -> True;\n"),(index+2))
                Disjunction _ _ ->
                    (((axiom_subcime (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (term_cime t1) ++ ");\n" ++
                    fk1 ++ "(True," ++ (term_cime t2) ++ ") -> True;\n" ++
                    "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++
                    ") -> " ++ fk2 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (axiom_subcime (quanti f2)) ++
                    "," ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ");\n" ++
                    fk2 ++ "(True,True," ++ (term_cime t1) ++ "," ++ 
                    (term_cime t2) ++ ") -> True;\n"),(index+2))
                Negation (Disjunction _ _) _ ->
                    (((axiom_subcime (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (term_cime t1) ++ ");\n" ++
                    fk1 ++ "(True," ++ (term_cime t2) ++ ") -> False;\n" ++
                    "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++
                    ") -> " ++ fk2 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (axiom_subcime (quanti f2)) ++
                    "," ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ");\n" ++
                    fk2 ++ "(True,False," ++ (term_cime t1) ++ "," ++ 
                    (term_cime t2) ++ ") -> True;\n"),(index+2))
                Predication predS2 ts2 _ ->
                    (((predSymStr predS2) ++ "(" ++ (terms_cime ts2) ++ 
                    ") ->" ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (term_cime t1) ++ "," ++
                    (terms_cime ts2) ++ ");\n" ++
                    fk1 ++ "(True," ++ (term_cime t2) ++ "," ++ 
                    (terms_cime ts2) ++ ") -> True;\n" ++
                    "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++
                    ") -> " ++ fk2 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (predSymStr predS2) ++ "(" ++
                    (terms_cime ts2) ++ ")," ++ (term_cime t1) ++ "," ++
                    (term_cime t2) ++ ");\n" ++
                    fk2 ++ "(True,True," ++ (term_cime t1) ++ "," ++
                    (term_cime t2) ++ ") -> True;\n"),(index+2))
                Negation (Predication predS2 ts2 _) _ ->
                    (((predSymStr predS2) ++ "(" ++ (terms_cime ts2) ++ 
                    ") ->" ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (term_cime t1) ++ "," ++
                    (terms_cime ts2) ++ ");\n" ++
                    fk1 ++ "(True," ++ (term_cime t2) ++ "," ++ 
                    (terms_cime ts2) ++ ") -> False;\n" ++
                    "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++
                    ") -> " ++ fk2 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (predSymStr predS2) ++ "(" ++
                    (terms_cime ts2) ++ ")," ++ (term_cime t1) ++ "," ++
                    (term_cime t2) ++ ");\n" ++
                    fk2 ++ "(True,False," ++ (term_cime t1) ++ "," ++
                    (term_cime t2) ++ ") -> True;\n"),(index+2))
                Strong_equation t3 t4 _ ->
                    (("eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (term_cime t1) ++ "," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ");\n" ++
                    fk1 ++ "(True," ++ (term_cime t2) ++ "," ++ 
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> True;\n" ++
                    "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (term_cime t3) ++ "," ++
                    (term_cime t1) ++ "," ++ (term_cime t2) ++ ");\n" ++
                    fk1 ++ "(True," ++ (term_cime t4) ++ "," ++ 
                    (term_cime t1) ++ "," ++ (term_cime t2) ++ ") -> True;\n"),
                    (index+2))
                Negation (Strong_equation t3 t4 _) _ ->
                    (("eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (term_cime t1) ++ "," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ");\n" ++
                    fk1 ++ "(True," ++ (term_cime t2) ++ "," ++ 
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> False;\n" ++
                    "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ "eq(" ++ (term_cime t3) ++ 
                    "," ++ (term_cime t4) ++ ")" ++ (term_cime t1) ++ "," ++ 
                    (term_cime t2) ++ ");\n" ++
                    fk1 ++ "(True,False," ++ 
                    (term_cime t1) ++ "," ++ (term_cime t2) ++ ") -> True;\n"),
                    (index+2))
                Existl_equation t3 t4 _ ->
                    (("eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (term_cime t1) ++ "," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ");\n" ++
                    fk1 ++ "(True," ++ (term_cime t2) ++ "," ++ 
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> True;\n" ++
                    "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (term_cime t3) ++ "," ++
                    (term_cime t1) ++ "," ++ (term_cime t2) ++ ");\n" ++
                    fk1 ++ "(True," ++ (term_cime t4) ++ "," ++ 
                    (term_cime t1) ++ "," ++ (term_cime t2) ++ ") -> True;\n"),
                    (index+2))
                Negation (Existl_equation t3 t4 _) _ ->
                    (("eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ (term_cime t1) ++ "," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ");\n" ++
                    fk1 ++ "(True," ++ (term_cime t2) ++ "," ++ 
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> False;\n" ++
                    "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ 
                    ") -> " ++ fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ 
                    (terms_cime ts1) ++ ")," ++ "eq(" ++ (term_cime t3) ++ 
                    "," ++ (term_cime t4) ++ ")" ++ (term_cime t1) ++ "," ++ 
                    (term_cime t2) ++ ");\n" ++
                    fk1 ++ "(True,False," ++ 
                    (term_cime t1) ++ "," ++ (term_cime t2) ++ ") -> True;\n"),
                    (index+2))
                _ -> error "CASL.CCC.TerminationProof.<impli_cime_p_eq_ex>"
          _ -> error "CASL.CCC.TerminationProof.<impli_cime_p>"
    Implication (Strong_equation t1 t2 _) f1 _ _ ->
        case (quanti f1) of
          Conjunction _ _ ->
              (((axiom_subcime (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_cime t1) ++ ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ ") -> True;\n"),(index+1))
          Negation (Conjunction _ _) _ ->
              (((axiom_subcime (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_cime t1) ++ ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ ") -> False;\n"),(index+1))
          Disjunction _ _ ->
              (((axiom_subcime (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_cime t1) ++ ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ ") -> True;\n"),(index+1))
          Negation (Disjunction _ _) _ ->
              (((axiom_subcime (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_cime t1) ++ ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ ") -> False;\n"),(index+1))
          Predication predS ts _ ->
              (((predSymStr predS)++"("++(terms_cime ts) ++ ") -> " ++
              fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (terms_cime ts) ++ 
              ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (terms_cime ts) ++
              ") -> True;\n"),(index+1))
          Negation (Predication predS ts _) _ ->
              (((predSymStr predS)++"("++(terms_cime ts) ++ ") -> " ++
              fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (terms_cime ts) ++ 
              ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (terms_cime ts) ++
              ") -> False;\n"),(index+1))
          Strong_equation t3 t4 _ ->
              (("eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t3) ++ "," ++ 
              (term_cime t4) ++ ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t3) ++ "," ++
              (term_cime t4) ++ ") -> True;\n"),(index + 1))
          Negation (Strong_equation t3 t4 _) _ ->
              (("eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t3) ++ "," ++ 
              (term_cime t4) ++ ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t3) ++ "," ++
              (term_cime t4) ++ ") -> False;\n"),(index + 1))
          Existl_equation t3 t4 _ ->
              (("eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t3) ++ "," ++ 
              (term_cime t4) ++ ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t3) ++ "," ++
              (term_cime t4) ++ ") -> True;\n"),(index + 1))
          Negation (Existl_equation t3 t4 _) _ ->
              (("eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t3) ++ "," ++ 
              (term_cime t4) ++ ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t3) ++ "," ++
              (term_cime t4) ++ ") -> False;\n"),(index + 1))
          Equivalence (Predication predS1 ts1 _) f2 _->
              case (quanti f2) of
                Conjunction _ _ ->
                    (((axiom_subcime (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++ "));\n"++
                    fk1 ++ "(" ++ (term_cime t2) ++ ",True) -> True;\n"),
                    (index+1))
                Negation (Conjunction _ _) _ ->
                    (((axiom_subcime (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++ "));\n"++
                    fk1 ++ "(" ++ (term_cime t2) ++ ",True) -> False;\n"),
                    (index+1))
                Disjunction _ _ ->
                    (((axiom_subcime (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++ "));\n"++
                    fk1 ++ "(" ++ (term_cime t2) ++ ",True) -> True;\n"),
                    (index+1))
                Negation (Disjunction _ _) _ ->
                    (((axiom_subcime (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++ "));\n"++
                    fk1 ++ "(" ++ (term_cime t2) ++ ",True) -> False;\n"),
                    (index+1))
                Predication predS2 ts2 _ ->
                    (((predSymStr predS2)++"("++(terms_cime ts2) ++ ") -> " ++
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++
                    (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++ ")," ++
                    (terms_cime ts2) ++ ");\n" ++
                    fk1++"("++(term_cime t2)++ ",True," ++ (terms_cime ts2) ++
                    ") -> True;\n"),(index + 1))
                Negation (Predication predS2 ts2 _) _ ->
                    (((predSymStr predS2)++"("++(terms_cime ts2) ++ ") -> " ++
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++
                    (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++ ")," ++
                    (terms_cime ts2) ++ ");\n" ++
                    fk1++"("++(term_cime t2)++ ",True," ++ (terms_cime ts2) ++
                    ") -> False;\n"),(index + 1))
                Strong_equation t3 t4 _ ->
                    (("eq("++(term_cime t3)++","++(term_cime t4)++") -> " ++
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++
                    (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++
                    ")," ++ (term_cime t3)++","++(term_cime t4) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ ",True," ++ 
                    (term_cime t3)++ "," ++ (term_cime t4) ++ ") -> " ++
                    "True;\n"),(index + 1))
                Negation (Strong_equation t3 t4 _) _ ->
                    (("eq("++(term_cime t3)++","++(term_cime t4)++") -> " ++
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++
                    (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++
                    ")," ++ (term_cime t3)++","++(term_cime t4) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ ",True," ++ 
                    (term_cime t3)++ "," ++ (term_cime t4) ++ ") -> " ++
                    "False;\n"),(index + 1))
                Existl_equation t3 t4 _ ->
                    (("eq("++(term_cime t3)++","++(term_cime t4)++") -> " ++
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++
                    (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++
                    ")," ++ (term_cime t3)++","++(term_cime t4) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ ",True," ++ 
                    (term_cime t3)++ "," ++ (term_cime t4) ++ ") -> " ++
                    "True;\n"),(index + 1))
                Negation (Existl_equation t3 t4 _) _ ->
                    (("eq("++(term_cime t3)++","++(term_cime t4)++") -> " ++
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++
                    (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++
                    ")," ++ (term_cime t3)++","++(term_cime t4) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ ",True," ++ 
                    (term_cime t3)++ "," ++ (term_cime t4) ++ ") -> " ++
                    "False;\n"),(index + 1))
                _ -> error "CASL.CCC.TerminationProof.<impli_cime_str_eq_p>"
          Equivalence (Strong_equation t3 t4 _) f2 _->
              case (quanti f2) of
                Conjunction _ _ ->
                    (((axiom_subcime (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ 
                    (term_cime t3) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ 
                    (term_cime t4) ++ ") -> True;\n" ++
                    "eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ "," ++
                    (axiom_subcime (quanti f2)) ++ "," ++ (term_cime t3) ++
                    "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ ",True," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> True;\n"),
                    (index+2))
                Negation (Conjunction _ _) _ ->
                    (((axiom_subcime (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ 
                    (term_cime t3) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ 
                    (term_cime t4) ++ ") -> False;\n" ++
                    "eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ "," ++
                    (axiom_subcime (quanti f2)) ++ "," ++ (term_cime t3) ++
                    "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ ",False," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> True;\n"),
                    (index+2))
                Disjunction _ _ ->
                    (((axiom_subcime (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ 
                    (term_cime t3) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ 
                    (term_cime t4) ++ ") -> True;\n" ++
                    "eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ "," ++
                    (axiom_subcime (quanti f2)) ++ "," ++ (term_cime t3) ++
                    "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ ",True," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> True;\n"),
                    (index+2))
                Negation (Disjunction _ _) _ ->
                    (((axiom_subcime (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ 
                    (term_cime t3) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ 
                    (term_cime t4) ++ ") -> False;\n" ++
                    "eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ "," ++
                    (axiom_subcime (quanti f2)) ++ "," ++ (term_cime t3) ++
                    "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ ",False," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> True;\n"),
                    (index+2))
                Predication predS ts _ ->
                    (((predSymStr predS)++"("++(terms_cime ts) ++ ") -> " ++
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t3) ++ 
                    "," ++ (terms_cime ts) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t4) ++
                    "," ++ (terms_cime ts) ++ ") -> True;\n" ++
                    "eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ "," ++ 
                    (predSymStr predS) ++ "(" ++ (terms_cime ts) ++ ")," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ ",True," ++ 
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> True;\n"),
                    (index + 2))
                Negation (Predication predS ts _) _ ->
                    (((predSymStr predS)++"("++(terms_cime ts) ++ ") -> " ++
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t3) ++ 
                    "," ++ (terms_cime ts) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t4) ++
                    "," ++ (terms_cime ts) ++ ") -> False;\n" ++
                    "eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ "," ++ 
                    (predSymStr predS) ++ "(" ++ (terms_cime ts) ++ ")," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ ",False," ++ 
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> True;\n"),
                    (index + 2))
                Strong_equation t5 t6 _ ->
                    (("eq("++(term_cime t5)++","++(term_cime t6)++") -> " ++
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t3) ++
                    "," ++ (term_cime t5) ++ "," ++ (term_cime t6) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t4) ++
                    "," ++ (term_cime t5) ++ "," ++ (term_cime t6) ++ 
                    ") -> True;\n" ++
                    "eq("++(term_cime t3)++","++(term_cime t4)++") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t5) ++
                    "," ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t6) ++
                    "," ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> True;\n"),(index + 2))
                Negation (Strong_equation t5 t6 _) _ ->
                    (("eq("++(term_cime t5)++","++(term_cime t6)++") -> " ++
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t3) ++
                    "," ++ (term_cime t5) ++ "," ++ (term_cime t6) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t4) ++
                    "," ++ (term_cime t5) ++ "," ++ (term_cime t6) ++ 
                    ") -> False;\n" ++
                    "eq("++(term_cime t3)++","++(term_cime t4)++") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ ",eq(" ++ (term_cime t5) ++
                    "," ++ (term_cime t6) ++ ")," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ ",False," ++ 
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> True;\n"),(index + 2))
                Existl_equation t5 t6 _ ->
                    (("eq("++(term_cime t5)++","++(term_cime t6)++") -> " ++
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t3) ++
                    "," ++ (term_cime t5) ++ "," ++ (term_cime t6) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t4) ++
                    "," ++ (term_cime t5) ++ "," ++ (term_cime t6) ++ 
                    ") -> True;\n" ++
                    "eq("++(term_cime t3)++","++(term_cime t4)++") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t5) ++
                    "," ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t6) ++
                    "," ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> True;\n"),(index + 2))
                Negation (Existl_equation t5 t6 _) _ ->
                    (("eq("++(term_cime t5)++","++(term_cime t6)++") -> " ++
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t3) ++
                    "," ++ (term_cime t5) ++ "," ++ (term_cime t6) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t4) ++
                    "," ++ (term_cime t5) ++ "," ++ (term_cime t6) ++ 
                    ") -> False;\n" ++
                    "eq("++(term_cime t3)++","++(term_cime t4)++") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ ",eq(" ++ (term_cime t5) ++
                    "," ++ (term_cime t6) ++ ")," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ ",False," ++ 
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> True;\n"),(index + 2))
                _ -> error "CASL.CCC.TerminationProof.<impli_cime_str_eq_str>"
          Equivalence (Existl_equation t3 t4 _) f2 _->
              case (quanti f2) of
                Conjunction _ _ ->
                    (((axiom_subcime (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ 
                    (term_cime t3) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ 
                    (term_cime t4) ++ ") -> True;\n" ++
                    "eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ "," ++
                    (axiom_subcime (quanti f2)) ++ "," ++ (term_cime t3) ++
                    "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ ",True," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> True;\n"),
                    (index+2))
                Negation (Conjunction _ _) _ ->
                    (((axiom_subcime (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ 
                    (term_cime t3) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ 
                    (term_cime t4) ++ ") -> False;\n" ++
                    "eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ "," ++
                    (axiom_subcime (quanti f2)) ++ "," ++ (term_cime t3) ++
                    "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ ",False," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> True;\n"),
                    (index+2))
                Disjunction _ _ ->
                    (((axiom_subcime (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ 
                    (term_cime t3) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ 
                    (term_cime t4) ++ ") -> True;\n" ++
                    "eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ "," ++
                    (axiom_subcime (quanti f2)) ++ "," ++ (term_cime t3) ++
                    "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ ",True," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> True;\n"),
                    (index+2))
                Negation (Disjunction _ _) _ ->
                    (((axiom_subcime (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ 
                    (term_cime t3) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ 
                    (term_cime t4) ++ ") -> False;\n" ++
                    "eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ "," ++
                    (axiom_subcime (quanti f2)) ++ "," ++ (term_cime t3) ++
                    "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ ",False," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> True;\n"),
                    (index+2))
                Predication predS ts _ ->
                    (((predSymStr predS)++"("++(terms_cime ts) ++ ") -> " ++
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t3) ++ 
                    "," ++ (terms_cime ts) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t4) ++
                    "," ++ (terms_cime ts) ++ ") -> True;\n" ++
                    "eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ "," ++ 
                    (predSymStr predS) ++ "(" ++ (terms_cime ts) ++ ")," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ ",True," ++ 
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> True;\n"),
                    (index + 2))
                Negation (Predication predS ts _) _ ->
                    (((predSymStr predS)++"("++(terms_cime ts) ++ ") -> " ++
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t3) ++ 
                    "," ++ (terms_cime ts) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t4) ++
                    "," ++ (terms_cime ts) ++ ") -> False;\n" ++
                    "eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ "," ++ 
                    (predSymStr predS) ++ "(" ++ (terms_cime ts) ++ ")," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ ",False," ++ 
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> True;\n"),
                    (index + 2))
                Strong_equation t5 t6 _ ->
                    (("eq("++(term_cime t5)++","++(term_cime t6)++") -> " ++
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t3) ++
                    "," ++ (term_cime t5) ++ "," ++ (term_cime t6) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t4) ++
                    "," ++ (term_cime t5) ++ "," ++ (term_cime t6) ++ 
                    ") -> True;\n" ++
                    "eq("++(term_cime t3)++","++(term_cime t4)++") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t5) ++
                    "," ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t6) ++
                    "," ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> True;\n"),(index + 2))
                Negation (Strong_equation t5 t6 _) _ ->
                    (("eq("++(term_cime t5)++","++(term_cime t6)++") -> " ++
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t3) ++
                    "," ++ (term_cime t5) ++ "," ++ (term_cime t6) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t4) ++
                    "," ++ (term_cime t5) ++ "," ++ (term_cime t6) ++ 
                    ") -> False;\n" ++
                    "eq("++(term_cime t3)++","++(term_cime t4)++") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ ",eq(" ++ (term_cime t5) ++
                    "," ++ (term_cime t6) ++ ")," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ ",False," ++ 
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> True;\n"),(index + 2))
                Existl_equation t5 t6 _ ->
                    (("eq("++(term_cime t5)++","++(term_cime t6)++") -> " ++
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t3) ++
                    "," ++ (term_cime t5) ++ "," ++ (term_cime t6) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t4) ++
                    "," ++ (term_cime t5) ++ "," ++ (term_cime t6) ++ 
                    ") -> True;\n" ++
                    "eq("++(term_cime t3)++","++(term_cime t4)++") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t5) ++
                    "," ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t6) ++
                    "," ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> True;\n"),(index + 2))
                Negation (Existl_equation t5 t6 _) _ ->
                    (("eq("++(term_cime t5)++","++(term_cime t6)++") -> " ++
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t3) ++
                    "," ++ (term_cime t5) ++ "," ++ (term_cime t6) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t4) ++
                    "," ++ (term_cime t5) ++ "," ++ (term_cime t6) ++ 
                    ") -> False;\n" ++
                    "eq("++(term_cime t3)++","++(term_cime t4)++") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ ",eq(" ++ (term_cime t5) ++
                    "," ++ (term_cime t6) ++ ")," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ ",False," ++ 
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> True;\n"),(index + 2))
                _ -> error "CASL.CCC.TerminationProof.<impli_cime_str_eq_ex>"
          _ -> error "CASL.CCC.TerminationProof.<impli_cime_str>"
    Implication (Existl_equation t1 t2 _) f1 _ _ ->
        case (quanti f1) of
          Conjunction _ _ ->
              (((axiom_subcime (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_cime t1) ++ ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ ") -> True;\n"),(index+1))
          Negation (Conjunction _ _) _ ->
              (((axiom_subcime (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_cime t1) ++ ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ ") -> False;\n"),(index+1))
          Disjunction _ _ ->
              (((axiom_subcime (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_cime t1) ++ ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ ") -> True;\n"),(index+1))
          Negation (Disjunction _ _) _ ->
              (((axiom_subcime (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_cime t1) ++ ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ ") -> False;\n"),(index+1))
          Predication predS ts _ ->
              (((predSymStr predS)++"("++(terms_cime ts) ++ ") -> " ++
              fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (terms_cime ts) ++ 
              ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (terms_cime ts) ++
              ") -> True;\n"),(index+1))
          Negation (Predication predS ts _) _ ->
              (((predSymStr predS)++"("++(terms_cime ts) ++ ") -> " ++
              fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (terms_cime ts) ++ 
              ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (terms_cime ts) ++
              ") -> False;\n"),(index+1))
          Strong_equation t3 t4 _ ->
              (("eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t3) ++ "," ++ 
              (term_cime t4) ++ ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t3) ++ "," ++
              (term_cime t4) ++ ") -> True;\n"),(index + 1))
          Negation (Strong_equation t3 t4 _) _ ->
              (("eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t3) ++ "," ++ 
              (term_cime t4) ++ ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t3) ++ "," ++
              (term_cime t4) ++ ") -> False;\n"),(index + 1))
          Existl_equation t3 t4 _ ->
              (("eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t3) ++ "," ++ 
              (term_cime t4) ++ ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t3) ++ "," ++
              (term_cime t4) ++ ") -> True;\n"),(index + 1))
          Negation (Existl_equation t3 t4 _) _ ->
              (("eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t3) ++ "," ++ 
              (term_cime t4) ++ ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t3) ++ "," ++
              (term_cime t4) ++ ") -> False;\n"),(index + 1))
          Equivalence (Predication predS1 ts1 _) f2 _->
              case (quanti f2) of
                Conjunction _ _ ->
                    (((axiom_subcime (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++ "));\n"++
                    fk1 ++ "(" ++ (term_cime t2) ++ ",True) -> True;\n"),
                    (index+1))
                Negation (Conjunction _ _) _ ->
                    (((axiom_subcime (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++ "));\n"++
                    fk1 ++ "(" ++ (term_cime t2) ++ ",True) -> False;\n"),
                    (index+1))
                Disjunction _ _ ->
                    (((axiom_subcime (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++ "));\n"++
                    fk1 ++ "(" ++ (term_cime t2) ++ ",True) -> True;\n"),
                    (index+1))
                Negation (Disjunction _ _) _ ->
                    (((axiom_subcime (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ 
                    (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++ "));\n"++
                    fk1 ++ "(" ++ (term_cime t2) ++ ",True) -> False;\n"),
                    (index+1))
                Predication predS2 ts2 _ ->
                    (((predSymStr predS2)++"("++(terms_cime ts2) ++ ") -> " ++
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++
                    (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++ ")," ++
                    (terms_cime ts2) ++ ");\n" ++
                    fk1++"("++(term_cime t2)++ ",True," ++ (terms_cime ts2) ++
                    ") -> True;\n"),(index + 1))
                Negation (Predication predS2 ts2 _) _ ->
                    (((predSymStr predS2)++"("++(terms_cime ts2) ++ ") -> " ++
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++
                    (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++ ")," ++
                    (terms_cime ts2) ++ ");\n" ++
                    fk1++"("++(term_cime t2)++ ",True," ++ (terms_cime ts2) ++
                    ") -> False;\n"),(index + 1))
                Strong_equation t3 t4 _ ->
                    (("eq("++(term_cime t3)++","++(term_cime t4)++") -> " ++
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++
                    (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++
                    ")," ++ (term_cime t3)++","++(term_cime t4) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ ",True," ++ 
                    (term_cime t3)++ "," ++ (term_cime t4) ++ ") -> " ++
                    "True;\n"),(index + 1))
                Negation (Strong_equation t3 t4 _) _ ->
                    (("eq("++(term_cime t3)++","++(term_cime t4)++") -> " ++
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++
                    (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++
                    ")," ++ (term_cime t3)++","++(term_cime t4) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ ",True," ++ 
                    (term_cime t3)++ "," ++ (term_cime t4) ++ ") -> " ++
                    "False;\n"),(index + 1))
                Existl_equation t3 t4 _ ->
                    (("eq("++(term_cime t3)++","++(term_cime t4)++") -> " ++
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++
                    (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++
                    ")," ++ (term_cime t3)++","++(term_cime t4) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ ",True," ++ 
                    (term_cime t3)++ "," ++ (term_cime t4) ++ ") -> " ++
                    "True;\n"),(index + 1))
                Negation (Existl_equation t3 t4 _) _ ->
                    (("eq("++(term_cime t3)++","++(term_cime t4)++") -> " ++
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++
                    (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++
                    ")," ++ (term_cime t3)++","++(term_cime t4) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ ",True," ++ 
                    (term_cime t3)++ "," ++ (term_cime t4) ++ ") -> " ++
                    "False;\n"),(index + 1))
                _ -> error "CASL.CCC.TerminationProof.<impli_cime_ex_eq_p>"
          Equivalence (Strong_equation t3 t4 _) f2 _->
              case (quanti f2) of
                Conjunction _ _ ->
                    (((axiom_subcime (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ 
                    (term_cime t3) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ 
                    (term_cime t4) ++ ") -> True;\n" ++
                    "eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ "," ++
                    (axiom_subcime (quanti f2)) ++ "," ++ (term_cime t3) ++
                    "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ ",True," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> True;\n"),
                    (index+2))
                Negation (Conjunction _ _) _ ->
                    (((axiom_subcime (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ 
                    (term_cime t3) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ 
                    (term_cime t4) ++ ") -> False;\n" ++
                    "eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ "," ++
                    (axiom_subcime (quanti f2)) ++ "," ++ (term_cime t3) ++
                    "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ ",False," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> True;\n"),
                    (index+2))
                Disjunction _ _ ->
                    (((axiom_subcime (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ 
                    (term_cime t3) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ 
                    (term_cime t4) ++ ") -> True;\n" ++
                    "eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ "," ++
                    (axiom_subcime (quanti f2)) ++ "," ++ (term_cime t3) ++
                    "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ ",True," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> True;\n"),
                    (index+2))
                Negation (Disjunction _ _) _ ->
                    (((axiom_subcime (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ 
                    (term_cime t3) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ 
                    (term_cime t4) ++ ") -> False;\n" ++
                    "eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ "," ++
                    (axiom_subcime (quanti f2)) ++ "," ++ (term_cime t3) ++
                    "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ ",False," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> True;\n"),
                    (index+2))
                Predication predS ts _ ->
                    (((predSymStr predS)++"("++(terms_cime ts) ++ ") -> " ++
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t3) ++ 
                    "," ++ (terms_cime ts) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t4) ++
                    "," ++ (terms_cime ts) ++ ") -> True;\n" ++
                    "eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ "," ++ 
                    (predSymStr predS) ++ "(" ++ (terms_cime ts) ++ ")," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ ",True," ++ 
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> True;\n"),
                    (index + 2))
                Negation (Predication predS ts _) _ ->
                    (((predSymStr predS)++"("++(terms_cime ts) ++ ") -> " ++
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t3) ++ 
                    "," ++ (terms_cime ts) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t4) ++
                    "," ++ (terms_cime ts) ++ ") -> False;\n" ++
                    "eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ "," ++ 
                    (predSymStr predS) ++ "(" ++ (terms_cime ts) ++ ")," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ ",False," ++ 
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> True;\n"),
                    (index + 2))
                Strong_equation t5 t6 _ ->
                    (("eq("++(term_cime t5)++","++(term_cime t6)++") -> " ++
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t3) ++
                    "," ++ (term_cime t5) ++ "," ++ (term_cime t6) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t4) ++
                    "," ++ (term_cime t5) ++ "," ++ (term_cime t6) ++ 
                    ") -> True;\n" ++
                    "eq("++(term_cime t3)++","++(term_cime t4)++") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t5) ++
                    "," ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t6) ++
                    "," ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> True;\n"),(index + 2))
                Negation (Strong_equation t5 t6 _) _ ->
                    (("eq("++(term_cime t5)++","++(term_cime t6)++") -> " ++
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t3) ++
                    "," ++ (term_cime t5) ++ "," ++ (term_cime t6) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t4) ++
                    "," ++ (term_cime t5) ++ "," ++ (term_cime t6) ++ 
                    ") -> False;\n" ++
                    "eq("++(term_cime t3)++","++(term_cime t4)++") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ ",eq(" ++ (term_cime t5) ++
                    "," ++ (term_cime t6) ++ ")," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ ",False," ++ 
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> True;\n"),(index + 2))
                Existl_equation t5 t6 _ ->
                    (("eq("++(term_cime t5)++","++(term_cime t6)++") -> " ++
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t3) ++
                    "," ++ (term_cime t5) ++ "," ++ (term_cime t6) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t4) ++
                    "," ++ (term_cime t5) ++ "," ++ (term_cime t6) ++ 
                    ") -> True;\n" ++
                    "eq("++(term_cime t3)++","++(term_cime t4)++") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t5) ++
                    "," ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t6) ++
                    "," ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> True;\n"),(index + 2))
                Negation (Existl_equation t5 t6 _) _ ->
                    (("eq("++(term_cime t5)++","++(term_cime t6)++") -> " ++
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t3) ++
                    "," ++ (term_cime t5) ++ "," ++ (term_cime t6) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t4) ++
                    "," ++ (term_cime t5) ++ "," ++ (term_cime t6) ++ 
                    ") -> False;\n" ++
                    "eq("++(term_cime t3)++","++(term_cime t4)++") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ ",eq(" ++ (term_cime t5) ++
                    "," ++ (term_cime t6) ++ ")," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ ",False," ++ 
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> True;\n"),(index + 2))
                _ -> error "CASL.CCC.TerminationProof.<impli_cime_ex_eq_str>"
          Equivalence (Existl_equation t3 t4 _) f2 _->
              case (quanti f2) of
                Conjunction _ _ ->
                    (((axiom_subcime (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ 
                    (term_cime t3) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ 
                    (term_cime t4) ++ ") -> True;\n" ++
                    "eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ "," ++
                    (axiom_subcime (quanti f2)) ++ "," ++ (term_cime t3) ++
                    "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ ",True," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> True;\n"),
                    (index+2))
                Negation (Conjunction _ _) _ ->
                    (((axiom_subcime (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ 
                    (term_cime t3) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ 
                    (term_cime t4) ++ ") -> False;\n" ++
                    "eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ "," ++
                    (axiom_subcime (quanti f2)) ++ "," ++ (term_cime t3) ++
                    "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ ",False," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> True;\n"),
                    (index+2))
                Disjunction _ _ ->
                    (((axiom_subcime (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ 
                    (term_cime t3) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ 
                    (term_cime t4) ++ ") -> True;\n" ++
                    "eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ "," ++
                    (axiom_subcime (quanti f2)) ++ "," ++ (term_cime t3) ++
                    "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ ",True," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> True;\n"),
                    (index+2))
                Negation (Disjunction _ _) _ ->
                    (((axiom_subcime (quanti f2)) ++ " -> " ++ 
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ 
                    (term_cime t3) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ 
                    (term_cime t4) ++ ") -> False;\n" ++
                    "eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++
                    ") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ "," ++
                    (axiom_subcime (quanti f2)) ++ "," ++ (term_cime t3) ++
                    "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ ",False," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> True;\n"),
                    (index+2))
                Predication predS ts _ ->
                    (((predSymStr predS)++"("++(terms_cime ts) ++ ") -> " ++
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t3) ++ 
                    "," ++ (terms_cime ts) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t4) ++
                    "," ++ (terms_cime ts) ++ ") -> True;\n" ++
                    "eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ "," ++ 
                    (predSymStr predS) ++ "(" ++ (terms_cime ts) ++ ")," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ ",True," ++ 
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> True;\n"),
                    (index + 2))
                Negation (Predication predS ts _) _ ->
                    (((predSymStr predS)++"("++(terms_cime ts) ++ ") -> " ++
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t3) ++ 
                    "," ++ (terms_cime ts) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t4) ++
                    "," ++ (terms_cime ts) ++ ") -> False;\n" ++
                    "eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ "," ++ 
                    (predSymStr predS) ++ "(" ++ (terms_cime ts) ++ ")," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ ",False," ++ 
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> True;\n"),
                    (index + 2))
                Strong_equation t5 t6 _ ->
                    (("eq("++(term_cime t5)++","++(term_cime t6)++") -> " ++
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t3) ++
                    "," ++ (term_cime t5) ++ "," ++ (term_cime t6) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t4) ++
                    "," ++ (term_cime t5) ++ "," ++ (term_cime t6) ++ 
                    ") -> True;\n" ++
                    "eq("++(term_cime t3)++","++(term_cime t4)++") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t5) ++
                    "," ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t6) ++
                    "," ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> True;\n"),(index + 2))
                Negation (Strong_equation t5 t6 _) _ ->
                    (("eq("++(term_cime t5)++","++(term_cime t6)++") -> " ++
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t3) ++
                    "," ++ (term_cime t5) ++ "," ++ (term_cime t6) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t4) ++
                    "," ++ (term_cime t5) ++ "," ++ (term_cime t6) ++ 
                    ") -> False;\n" ++
                    "eq("++(term_cime t3)++","++(term_cime t4)++") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ ",eq(" ++ (term_cime t5) ++
                    "," ++ (term_cime t6) ++ ")," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ ",False," ++ 
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> True;\n"),(index + 2))
                Existl_equation t5 t6 _ ->
                    (("eq("++(term_cime t5)++","++(term_cime t6)++") -> " ++
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t3) ++
                    "," ++ (term_cime t5) ++ "," ++ (term_cime t6) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t4) ++
                    "," ++ (term_cime t5) ++ "," ++ (term_cime t6) ++ 
                    ") -> True;\n" ++
                    "eq("++(term_cime t3)++","++(term_cime t4)++") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t5) ++
                    "," ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t6) ++
                    "," ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> True;\n"),(index + 2))
                Negation (Existl_equation t5 t6 _) _ ->
                    (("eq("++(term_cime t5)++","++(term_cime t6)++") -> " ++
                    fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (term_cime t3) ++
                    "," ++ (term_cime t5) ++ "," ++ (term_cime t6) ++ ");\n" ++
                    fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (term_cime t4) ++
                    "," ++ (term_cime t5) ++ "," ++ (term_cime t6) ++ 
                    ") -> False;\n" ++
                    "eq("++(term_cime t3)++","++(term_cime t4)++") -> " ++
                    fk2 ++ "(" ++ (term_cime t1) ++ ",eq(" ++ (term_cime t5) ++
                    "," ++ (term_cime t6) ++ ")," ++
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ ");\n" ++
                    fk2 ++ "(" ++ (term_cime t2) ++ ",False," ++ 
                    (term_cime t3) ++ "," ++ (term_cime t4) ++ 
                    ") -> True;\n"),(index + 2))
                _ -> error "CASL.CCC.TerminationProof.<impli_cime_ex_eq_ex>"
          _ -> error "CASL.CCC.TerminationProof.<impli_cime_ex>"
    _ -> error "CASL.CCC.TerminationProof.<impli_cime>"
  where fk1 = "af" ++ (show index)
        fk2 = "af" ++ (show $ index +1)


{- transform Equivalence to cime: 
   (p(t_1,...,t_m) <=> phi)
     Example:
             p(t_1,...,t_m) <=> f(tt_1,...,tt_n)=t
     cime --> p(t_1,...,t_m)  => f(tt_1,...,tt_n)=t --> 
                 f(tt_1,...,tt_n) -> U1(p(t_1,...,t_m),tt_1,...,tt_n);
                 U1(True,tt_1,...,tt_n) -> t;
          --> f(tt_1,...,tt_n)=t => p(t_1,...,t_m)  --> 
                 p(t_1,...,t_m) -> U2(f(tt_1,...,tt_n),t_1,...,t_m);
                 U2(t,t_1,...t_m) -> True; 
-}
equiv_cime :: Int -> FORMULA f -> (Cime,Int)
equiv_cime index f =
  case (quanti f) of
    Equivalence (Predication predS1 ts1 _) f1 _ ->
        case (quanti f1) of
          Conjunction _ _ ->
              (((axiom_subcime (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++ 
              "));\n" ++
              fk1 ++ "(True) -> True;\n"),(index+1))
          Negation (Conjunction _ _) _ ->
              (((axiom_subcime (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++ 
              "));\n" ++
              fk1 ++ "(True) -> False;\n"),(index+1))
          Disjunction _ _ ->
              (((axiom_subcime (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++ 
              "));\n" ++
              fk1 ++ "(True) -> True;\n"),(index+1))
          Negation (Disjunction _ _) _ ->
              (((axiom_subcime (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++ 
              "));\n" ++
              fk1 ++ "(True) -> False;\n"),(index+1))              
          Predication predS2 ts2 _ ->
              (((predSymStr predS2) ++ "(" ++ (terms_cime ts2) ++ ") -> " ++
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++ 
              ")," ++ (terms_cime ts2) ++ ");\n" ++
              fk1 ++ "(True," ++ (terms_cime ts2) ++ ") -> True;\n"),
              (index +1))
          Negation (Predication predS2 ts2 _) _ ->           -- !!
              (((predSymStr predS2) ++ "(" ++ (terms_cime ts2) ++ ") -> " ++
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++ 
              ")," ++ (terms_cime ts2) ++ ");\n" ++
              fk1 ++ "(True," ++ (terms_cime ts2) ++ ") -> False;\n"),
              (index +1))
          Strong_equation t1 t2 _ -> 
              (("eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ") -> " ++
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++
              ")," ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ");\n" ++
              fk1++"(True,"++(term_cime t1)++","++(term_cime t2)++") -> " ++
              "True;\n"),(index + 1))
          Negation (Strong_equation t1 t2 _) _ ->
              (("eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ") -> " ++
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++
              ")," ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ");\n" ++
              fk1 ++ "(True," ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ 
              ") -> False;\n"),(index +1))
          Existl_equation t1 t2 _ -> 
              (("eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ") -> " ++
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++
              ")," ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ");\n" ++
              fk1++"(True,"++(term_cime t1)++","++(term_cime t2)++") -> " ++
              "True;\n"),(index + 1))
          Negation (Existl_equation t1 t2 _) _ ->
              (("eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ") -> " ++
              fk1 ++ "(" ++ (predSymStr predS1) ++ "(" ++ (terms_cime ts1) ++
              ")," ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ");\n" ++
              fk1 ++ "(True," ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ 
              ") -> False;\n"),(index +1))
          _ -> error "CASL.CCC.TerminationProof.<equiv_cime_pred>"
    Equivalence (Strong_equation t1 t2 _) f1 _ ->
        case (quanti f1) of
          Conjunction _ _ ->
              (((axiom_subcime (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_cime t1) ++ ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ ") -> True;\n" ++
              "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ") -> " ++
              fk2 ++ "(" ++ (axiom_subcime (quanti f1)) ++ "," ++
              (term_cime t1) ++ "," ++ (term_cime t2) ++ ");\n" ++
              fk2 ++ "(True," ++ (term_cime t1) ++ "," ++
              (term_cime t2) ++ ") -> True;\n"),(index+2))
          Negation (Conjunction _ _) _ ->
              (((axiom_subcime (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_cime t1) ++ ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ ") -> False;\n" ++
              "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ") -> " ++
              fk2 ++ "(" ++ (axiom_subcime (quanti f1)) ++ "," ++
              (term_cime t1) ++ "," ++ (term_cime t2) ++ ");\n" ++
              fk2 ++ "(False," ++ (term_cime t1) ++ "," ++
              (term_cime t2) ++ ") -> True;\n"),(index+2))
          Disjunction _ _ ->
              (((axiom_subcime (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_cime t1) ++ ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ ") -> True;\n" ++
              "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ") -> " ++
              fk2 ++ "(" ++ (axiom_subcime (quanti f1)) ++ "," ++
              (term_cime t1) ++ "," ++ (term_cime t2) ++ ");\n" ++
              fk2 ++ "(True," ++ (term_cime t1) ++ "," ++
              (term_cime t2) ++ ") -> True;\n"),(index+2))
          Negation (Disjunction _ _) _ ->
              (((axiom_subcime (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_cime t1) ++ ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ ") -> False;\n" ++
              "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ") -> " ++
              fk2 ++ "(" ++ (axiom_subcime (quanti f1)) ++ "," ++
              (term_cime t1) ++ "," ++ (term_cime t2) ++ ");\n" ++
              fk2 ++ "(False," ++ (term_cime t1) ++ "," ++
              (term_cime t2) ++ ") -> True;\n"),(index+2))
          Predication predS ts _ ->
              (((predSymStr predS) ++ "(" ++ (terms_cime ts) ++ ") -> " ++
              fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (terms_cime ts) ++ 
              ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (terms_cime ts) ++ 
              ") -> True;\n" ++
              "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ") -> " ++
              fk2 ++ "(" ++ (predSymStr predS) ++ "(" ++ (terms_cime ts) ++
              ")," ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ");\n" ++
              fk2 ++ "(True," ++ (term_cime t1) ++ "," ++ (term_cime t2) ++
              ") -> True;\n"),(index +2))
          Negation (Predication predS ts _) _ ->
              (((predSymStr predS) ++ "(" ++ (terms_cime ts) ++ ") -> " ++
              fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (terms_cime ts) ++ 
              ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (terms_cime ts) ++ 
              ") -> False;\n" ++
              "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ") -> " ++
              fk2 ++ "(" ++ (predSymStr predS) ++ "(" ++ (terms_cime ts) ++
              ")," ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ");\n" ++
              fk2 ++ "(False," ++ (term_cime t1) ++ "," ++ (term_cime t2) ++
              ") -> True;\n"),(index +2))
          Strong_equation t3 t4 _ ->
              (("eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_cime t1)++ "," ++ (term_cime t3) ++ 
              "," ++ (term_cime t4) ++ ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ ","++ (term_cime t3) ++ 
              "," ++ (term_cime t4) ++ ") -> " ++ "True;\n" ++ 
              "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ") -> " ++
              fk1 ++ "(" ++ (term_cime t3)++ "," ++ (term_cime t1) ++ 
              "," ++ (term_cime t2) ++ ");\n" ++
              fk1 ++ "(" ++ (term_cime t4) ++ ","++ (term_cime t1) ++ 
              "," ++ (term_cime t2) ++ ") -> " ++ "True;\n"),(index + 2))
          Negation (Strong_equation t3 t4 _) _ ->
              (("eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_cime t1)++ "," ++ (term_cime t3) ++ 
              "," ++ (term_cime t4) ++ ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ ","++ (term_cime t3) ++ 
              "," ++ (term_cime t4) ++ ") -> " ++ "False;\n" ++ 
              "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ") -> " ++
              fk1 ++ "(eq(" ++ (term_cime t3)++ "," ++ (term_cime t4) ++
              ")," ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ");\n" ++
              fk1 ++ "(False," ++ (term_cime t1) ++ 
              "," ++ (term_cime t2) ++ ") -> " ++ "True;\n"),(index + 2))
          Existl_equation t3 t4 _ ->
              (("eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_cime t1)++ "," ++ (term_cime t3) ++ 
              "," ++ (term_cime t4) ++ ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ ","++ (term_cime t3) ++ 
              "," ++ (term_cime t4) ++ ") -> " ++ "True;\n" ++ 
              "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ") -> " ++
              fk1 ++ "(" ++ (term_cime t3)++ "," ++ (term_cime t1) ++ 
              "," ++ (term_cime t2) ++ ");\n" ++
              fk1 ++ "(" ++ (term_cime t4) ++ ","++ (term_cime t1) ++ 
              "," ++ (term_cime t2) ++ ") -> " ++ "True;\n"),(index + 2))
          Negation (Existl_equation t3 t4 _) _ ->
              (("eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_cime t1)++ "," ++ (term_cime t3) ++ 
              "," ++ (term_cime t4) ++ ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ ","++ (term_cime t3) ++ 
              "," ++ (term_cime t4) ++ ") -> " ++ "False;\n" ++ 
              "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ") -> " ++
              fk1 ++ "(eq(" ++ (term_cime t3)++ "," ++ (term_cime t4) ++
              ")," ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ");\n" ++
              fk1 ++ "(False," ++ (term_cime t1) ++ 
              "," ++ (term_cime t2) ++ ") -> " ++ "True;\n"),(index + 2))
          _ -> error "CASL.CCC.TerminationProof.<equiv_cime_str>"
    Equivalence (Existl_equation t1 t2 _) f1 _ ->
        case (quanti f1) of
          Conjunction _ _ ->
              (((axiom_subcime (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_cime t1) ++ ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ ") -> True;\n" ++
              "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ") -> " ++
              fk2 ++ "(" ++ (axiom_subcime (quanti f1)) ++ "," ++
              (term_cime t1) ++ "," ++ (term_cime t2) ++ ");\n" ++
              fk2 ++ "(True," ++ (term_cime t1) ++ "," ++
              (term_cime t2) ++ ") -> True;\n"),(index+2))
          Negation (Conjunction _ _) _ ->
              (((axiom_subcime (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_cime t1) ++ ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ ") -> False;\n" ++
              "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ") -> " ++
              fk2 ++ "(" ++ (axiom_subcime (quanti f1)) ++ "," ++
              (term_cime t1) ++ "," ++ (term_cime t2) ++ ");\n" ++
              fk2 ++ "(False," ++ (term_cime t1) ++ "," ++
              (term_cime t2) ++ ") -> True;\n"),(index+2))
          Disjunction _ _ ->
              (((axiom_subcime (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_cime t1) ++ ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ ") -> True;\n" ++
              "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ") -> " ++
              fk2 ++ "(" ++ (axiom_subcime (quanti f1)) ++ "," ++
              (term_cime t1) ++ "," ++ (term_cime t2) ++ ");\n" ++
              fk2 ++ "(True," ++ (term_cime t1) ++ "," ++
              (term_cime t2) ++ ") -> True;\n"),(index+2))
          Negation (Disjunction _ _) _ ->
              (((axiom_subcime (quanti f1)) ++ " -> " ++ 
              fk1 ++ "(" ++ (term_cime t1) ++ ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ ") -> False;\n" ++
              "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ") -> " ++
              fk2 ++ "(" ++ (axiom_subcime (quanti f1)) ++ "," ++
              (term_cime t1) ++ "," ++ (term_cime t2) ++ ");\n" ++
              fk2 ++ "(False," ++ (term_cime t1) ++ "," ++
              (term_cime t2) ++ ") -> True;\n"),(index+2))
          Predication predS ts _ ->
              (((predSymStr predS) ++ "(" ++ (terms_cime ts) ++ ") -> " ++
              fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (terms_cime ts) ++ 
              ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (terms_cime ts) ++ 
              ") -> True;\n" ++
              "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ") -> " ++
              fk2 ++ "(" ++ (predSymStr predS) ++ "(" ++ (terms_cime ts) ++
              ")," ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ");\n" ++
              fk2 ++ "(True," ++ (term_cime t1) ++ "," ++ (term_cime t2) ++
              ") -> True;\n"),(index +2))
          Negation (Predication predS ts _) _ ->
              (((predSymStr predS) ++ "(" ++ (terms_cime ts) ++ ") -> " ++
              fk1 ++ "(" ++ (term_cime t1) ++ "," ++ (terms_cime ts) ++ 
              ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ "," ++ (terms_cime ts) ++ 
              ") -> False;\n" ++
              "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ") -> " ++
              fk2 ++ "(" ++ (predSymStr predS) ++ "(" ++ (terms_cime ts) ++
              ")," ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ");\n" ++
              fk2 ++ "(False," ++ (term_cime t1) ++ "," ++ (term_cime t2) ++
              ") -> True;\n"),(index +2))
          Strong_equation t3 t4 _ ->
              (("eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_cime t1)++ "," ++ (term_cime t3) ++ 
              "," ++ (term_cime t4) ++ ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ ","++ (term_cime t3) ++ 
              "," ++ (term_cime t4) ++ ") -> " ++ "True;\n" ++ 
              "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ") -> " ++
              fk1 ++ "(" ++ (term_cime t3)++ "," ++ (term_cime t1) ++ 
              "," ++ (term_cime t2) ++ ");\n" ++
              fk1 ++ "(" ++ (term_cime t4) ++ ","++ (term_cime t1) ++ 
              "," ++ (term_cime t2) ++ ") -> " ++ "True;\n"),(index + 2))
          Negation (Strong_equation t3 t4 _) _ ->
              (("eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_cime t1)++ "," ++ (term_cime t3) ++ 
              "," ++ (term_cime t4) ++ ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ ","++ (term_cime t3) ++ 
              "," ++ (term_cime t4) ++ ") -> " ++ "False;\n" ++ 
              "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ") -> " ++
              fk1 ++ "(eq(" ++ (term_cime t3)++ "," ++ (term_cime t4) ++
              ")," ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ");\n" ++
              fk1 ++ "(False," ++ (term_cime t1) ++ 
              "," ++ (term_cime t2) ++ ") -> " ++ "True;\n"),(index + 2))
          Existl_equation t3 t4 _ ->
              (("eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_cime t1)++ "," ++ (term_cime t3) ++ 
              "," ++ (term_cime t4) ++ ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ ","++ (term_cime t3) ++ 
              "," ++ (term_cime t4) ++ ") -> " ++ "True;\n" ++ 
              "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ") -> " ++
              fk1 ++ "(" ++ (term_cime t3)++ "," ++ (term_cime t1) ++ 
              "," ++ (term_cime t2) ++ ");\n" ++
              fk1 ++ "(" ++ (term_cime t4) ++ ","++ (term_cime t1) ++ 
              "," ++ (term_cime t2) ++ ") -> " ++ "True;\n"),(index + 2))
          Negation (Existl_equation t3 t4 _) _ ->
              (("eq(" ++ (term_cime t3) ++ "," ++ (term_cime t4) ++ ") -> " ++
              fk1 ++ "(" ++ (term_cime t1)++ "," ++ (term_cime t3) ++ 
              "," ++ (term_cime t4) ++ ");\n" ++
              fk1 ++ "(" ++ (term_cime t2) ++ ","++ (term_cime t3) ++ 
              "," ++ (term_cime t4) ++ ") -> " ++ "False;\n" ++ 
              "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ") -> " ++
              fk1 ++ "(eq(" ++ (term_cime t3)++ "," ++ (term_cime t4) ++
              ")," ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ");\n" ++
              fk1 ++ "(False," ++ (term_cime t1) ++ 
              "," ++ (term_cime t2) ++ ") -> " ++ "True;\n"),(index + 2))
          _ -> error "CASL.CCC.TerminationProof.<equiv_cime_exi>"
    _ -> error "CASL.CCC.TerminationProof.<equiv_cime>"
  where fk1 = "af" ++ (show index)
        fk2 = "af" ++ (show $ index + 1)
 

impli_equiv_cime :: Int -> FORMULA f -> (Cime,Int)
impli_equiv_cime index f = 
  case (quanti f) of
    Implication _ _ _ _ -> impli_cime index f
    Equivalence _ _ _ -> equiv_cime index f
    _ -> error "CASL.CCC.TerminationProof.<impli_equiv_cime2>"


{- transform a axiom to cime (f_str)
-}
axiom_cime :: FORMULA f -> Cime
axiom_cime f = 
  case (quanti f) of
    Quantification _ _ f' _ -> axiom_cime f'
    Conjunction fs _ -> 
        conj_cime fs ++ " -> True"
    Disjunction fs _ -> 
        disj_cime fs ++ " -> True"
    Negation f' _ ->
        case f' of
          Conjunction fs _ ->
              conj_cime fs ++ " -> False"
          Disjunction fs _ ->
              disj_cime fs ++ " -> False"
          Predication p_s ts _ -> 
              ((predSymStr p_s) ++ "(" ++ (terms_cime ts) ++ ") -> False")
          Existl_equation t1 t2 _ -> 
              "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ") -> False"
          Strong_equation t1 t2 _ -> 
              "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ") -> False"
          Definedness _ _ -> ""           -- not implement
          _ -> error "CASL.CCC.TerminationProof.<Axioms_Negation>"
    True_atom _ -> 
        error "CASL.CCC.TerminationProof.<Axioms_True>"     
    False_atom _ -> 
        error "CASL.CCC.TerminationProof.<Axioms_False>"
    Predication p_s ts _ -> 
        ((predSymStr p_s) ++ "(" ++ (terms_cime ts) ++ ") -> True")
    Definedness _ _ -> 
        error "CASL.CCC.TerminationProof.<Axioms_Definedness>"
    Existl_equation t1 t2 _ -> 
        (term_cime t1) ++ " -> " ++ (term_cime t2)
    Strong_equation t1 t2 _ -> 
        (term_cime t1) ++ " -> " ++ (term_cime t2)                   
    _ -> error "CASL.CCC.TerminationProof.<Axioms>"
--  where termsStr ts = if null ts 
--                    then error "CASL.CCC.TerminationProof.axiom_cime"
--                    else tail $ concat $ map (\s->","++s) $ map term_cime ts


{- transform a axiom to subcime
-}
axiom_subcime :: FORMULA f -> Cime
axiom_subcime f = 
  case (quanti f) of
    Quantification _ _ f' _ -> axiom_subcime f'
    Conjunction fs _ -> 
        conj_cime fs
    Disjunction fs _ -> 
        disj_cime fs
    Negation f' _ ->
        case f' of
          Conjunction fs _ ->
              "not(" ++ conj_cime fs ++ ")"
          Disjunction fs _ ->
              "not(" ++ disj_cime fs ++ ")"
          Predication p_s ts _ -> 
              "not(" ++ (predSymStr p_s) ++ "(" ++ (terms_cime ts) ++ "))"
          Existl_equation t1 t2 _ -> 
              "not(eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ "))"
          Strong_equation t1 t2 _ -> 
              "not(eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ "))"
          Definedness _ _ -> 
              ""           -- not implement
          _ -> error "CASL.CCC.TerminationProof.cime_subcime.<Negation>"
    True_atom _ -> 
        "True"     
    False_atom _ -> 
        "False"
    Predication p_s ts _ -> 
        (predSymStr p_s) ++ "(" ++ (terms_cime ts) ++ ")"
    Definedness _ _ -> 
        error "CASL.CCC.TerminationProof.<Axioms_Definedness>"
    Existl_equation t1 t2 _ -> 
        "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ")"
    Strong_equation t1 t2 _ -> 
        "eq(" ++ (term_cime t1) ++ "," ++ (term_cime t2) ++ ")"
    _ -> error "CASL.CCC.TerminationProof.axiom_subcime.<Axioms>"


conj_cime :: [FORMULA f] -> Cime
conj_cime fs =
  if length fs == 2 then ("and(" ++ (axiom_subcime $ head fs) ++ "," ++
                                   (axiom_subcime $ last fs) ++ ")")
  else ("and(" ++ (axiom_cime $ head fs) ++ "," ++
                  (conj_cime $ tail fs) ++ ")")

disj_cime :: [FORMULA f] -> Cime
disj_cime fs =
  if length fs == 2 then ("or(" ++ (axiom_subcime $ head fs) ++ "," ++
                                  (axiom_subcime $ last fs) ++ ")")
  else ("or(" ++ (axiom_cime $ head fs) ++ "," ++
                 (conj_cime $ tail fs) ++ ")")


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


terms_cime :: [TERM f] -> Cime
terms_cime ts = 
    if null ts then ""
    else tail $ concat $ map (\s->","++s) $ map term_cime ts



