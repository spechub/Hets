{- | 
Module      :  $Header$
Description :  termination proofs for equation systems, using AProVE
Copyright   :  (c) Mingyi Liu and Till Mossakowski and Uni Bremen 2004-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  xinga@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Termination proofs for equation systems, using AProVE
-}

module CASL.CCC.TerminationProof where

import CASL.ToDoc ()
import CASL.AS_Basic_CASL     
import Common.DocUtils
import CASL.CCC.TermFormula
import Common.Id
import System.Cmd
import System.IO.Unsafe
-- import Debug.Trace
import System.Environment
import Data.List (nub)

{- 
   Automatic termination proof
   using AProVE, see http://aprove.informatik.rwth-aachen.de/

   interface to AProVE system, using system
   translate CASL signature to AProVE Input Language, 
   CASL formulas to AProVE term rewrite systems(TRS),
   see http://aprove.informatik.rwth-aachen.de/help/html/in/trs.html
-}

terminationProof :: (PosItem f, Pretty f, Eq f) => 
                    [FORMULA f] -> Maybe Bool
terminationProof fs
    | null fs = Just True
    | proof == "YES\n" = Just True
    | proof == "MAYBE\n" = Nothing
    | proof == "NO\n" = Just False
    | otherwise = error "CASL.CCC.TerminationProof.<terminationProof>"
    where
    allVar vs = nub $ concat vs   
    varsStr vars str                               
        | null vars = str
        | otherwise = if null str then varsStr (tail vars) (tokStr $ head vars)
                      else varsStr (tail vars) (str ++ " " ++ 
                                                (tokStr $ head vars))
    axiomTrs axs str
        | null axs = str
--        | is_impli_equiv $ head axs = 
--            axiomTrs (tail axs) (str ++ (impli_equiv_trs $ (head axs)) ++ "\n")
        | otherwise = 
            axiomTrs (tail axs) (str ++ (axiom_trs $ (head axs)) ++ "\n")
{-
    axiomStr axs str
        | null axs = str
        | otherwise = 
            axiomStr (tail axs) (str ++ (axiom_trs $ (head axs)) ++ "\n")
    impli_equiv = filter is_impli_equiv fs
    n_impli_equiv = filter (not.is_impli_equiv) fs
    auxAxstr afs str
        | null afs = str
        | otherwise =
              auxAxstr (tail afs) (str ++ (impli_equiv_trs (head afs)))
    axAux = auxAxstr impli_equiv ""
 -}  
    axhead = "(RULES\neq(t1,t1) -> true\n" ++ 
             "eq(t1,t2) -> false\n" ++
             "when_else(t1,true,t2) -> t1\n" ++ 
             "when_else(t1,false,t2) -> t2\n"
    c_vars = ("(VAR t1 t2 " ++ (varsStr (allVar $ map varOfAxiom $ 
                                fs) "") ++ ")\n")
{-
    c_axms = if null n_impli_equiv 
             then (axhead ++ axAux ++ ")\n")
             else (axhead ++ (axiomStr n_impli_equiv "") ++ axAux ++ ")\n")
             -}
    c_axms = axhead ++ (axiomTrs fs "") ++ ")\n"
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


-- | get the name of a operation symbol
opSymName :: OP_SYMB -> String 
opSymName os = case os of
                Op_name on -> idStr on
                Qual_op_name on _ _ -> idStr on


-- | get the name of a predicate symbol 
predSymName :: PRED_SYMB -> String
predSymName ps = case ps of 
                  Pred_name pn -> idStr pn 
                  Qual_pred_name pn _ _ -> idStr pn


-- | translate a casl term to a term of TRS(Terme Rewrite Systems)
term_trs :: TERM f -> String
term_trs t = 
  case (term t) of
    Simple_id simid -> tokStr simid
    Qual_var var _ _ -> tokStr var
    Application (Op_name opn) _ _ ->
        idStr opn
    Application (Qual_op_name opn _ _) ts _ -> 
        if null ts then (idStr opn)
        else ((idStr opn) ++ "(" ++ terms_pa ts ++")")
    Sorted_term t' _ _ ->
        term_trs t'
    Cast t' _ _ ->
        term_trs t'  
    Conditional t1 f t2 _ -> 
        ("when_else("++(term_trs t1)++","++
         (t_f_str f)++","++(term_trs t2)++")")
    _ -> error "CASL.CCC.TerminationProof.<term_trs>"
  where t_f_str f=case f of                     --  condition of a term
                    Strong_equation t1 t2 _ -> 
                        ("eq("++(term_trs t1)++","++(term_trs t2)++")")
                    Predication ps ts _ ->
                        if null ts then predSymName ps
                        else ((predSymName ps) ++ "(" ++
                              (terms_pa ts) ++ ")")
                    _ -> error "CASL.CCC.TerminationProof.<term_trs_cond>"


-- | translate a list of casl terms to the patterns of a term in TRS
terms_pa :: [TERM f] -> String
terms_pa ts = 
    if null ts then ""
    else tail $ concat $ map (\s->","++s) $ map term_trs ts
    
    
-- | translate a casl axiom (without conditions) to TRS-rule,
-- | a rule is represented by "A -> B" in Term Rewrite Systems,
-- | and the arrow "->" can occur only once in a rule. 
axiom_trs :: FORMULA f -> String
axiom_trs f = 
  case (quanti f) of
    Quantification _ _ f' _ -> axiom_trs f'
    Conjunction fs _ ->
        conj_sub fs ++ " -> true"
    Disjunction fs _ ->
        disj_sub fs ++ " -> true"
    Implication f1 f2 _ _ ->
        case f2 of 
          Equivalence f3 f4 _ ->
              (axiom_trs f4) ++  " | " ++
              (axiom_trs f3) ++ ", " ++
              (axiom_trs f1)
          _ -> 
              (axiom_trs f2) ++  " | " ++
              (axiom_trs f1)
    Equivalence f1 f2 _ ->
         (axiom_trs f2) ++ " | " ++
         (axiom_trs f1)
    Negation f' _ ->
        case f' of
          Conjunction fs _ ->
              conj_sub fs ++ " -> false"
          Disjunction fs _ ->
              disj_sub fs ++ " -> false"
          Predication p_s ts _ ->
              if null ts 
              then (predSymName p_s) ++ " -> false"
              else (predSymName p_s) ++ "(" ++ (terms_pa ts) ++ ") -> false"
          Strong_equation t1 t2 _ -> 
              "eq(" ++ (term_trs t1) ++ "," ++ (term_trs t2) ++ ") -> false"
          Definedness t _ -> 
              (term_trs t) ++ " -> undefined"
          _ -> error "CASL.CCC.TerminationProof.<axiom_trs_Negation>"
    Predication p_s ts _ ->
        if null ts then (predSymName p_s) ++ " -> true"
        else (predSymName p_s) ++ "(" ++ (terms_pa ts) ++ ") -> true"
    Definedness t _ ->
        (term_trs t) ++ " -> defined"
    Strong_equation t1 t2 _ ->
        case t2 of 
          Conditional tt1 ff tt2 _ ->
              (term_trs t1) ++ " -> " ++ (term_trs tt1) ++ " | " ++
              (axiom_sub ff) ++ " -> true\n" ++  
              (term_trs t1) ++ " -> " ++ (term_trs tt2) ++ " | " ++
              (axiom_sub ff) ++ " -> false"  
          _ -> if isApp t1 
               then (term_trs t1) ++ " -> " ++ (term_trs t2)
               else "eq(" ++ (term_trs t1) ++ "," ++ (term_trs t2) ++ 
                    ") -> true"          
    _ -> error "CASL.CCC.TerminationProof.<axiom_trs>"


-- | translate a casl axiom(without conditions) to a subrule of TRS,
-- | the arrow " -> " occurs not in a subrule.
axiom_sub :: FORMULA f -> String
axiom_sub f = 
  case (quanti f) of
    Quantification _ _ f' _ -> axiom_sub f'
    Conjunction fs _ -> 
        conj_sub fs
    Disjunction fs _ -> 
        disj_sub fs
    Negation f' _ ->
        case f' of
          Conjunction fs _ ->
              "not(" ++ conj_sub fs ++ ")"
          Disjunction fs _ ->
              "not(" ++ disj_sub fs ++ ")"
          Predication p_s ts _ ->
              if null ts then "not(" ++ (predSymName p_s) ++ ")"
              else "not(" ++ (predSymName p_s) ++ "(" ++ (terms_pa ts) ++ "))"
          Strong_equation t1 t2 _ -> 
              "not(eq(" ++ (term_trs t1) ++ "," ++ (term_trs t2) ++ "))"
          _ -> error "CASL.CCC.TerminationProof.str_substr.<Negation>"
    True_atom _ -> 
        "true"     
    False_atom _ -> 
        "false"
    Predication p_s ts _ ->
        if null ts then (predSymName p_s)
        else (predSymName p_s) ++ "(" ++ (terms_pa ts) ++ ")"
    Definedness t _ -> 
        (term_trs t) ++ " -> defined"
    Strong_equation t1 t2 _ -> 
        "eq(" ++ (term_trs t1) ++ "," ++ (term_trs t2) ++ ")"
    _ -> error "CASL.CCC.TerminationProof.axiom_sub.<axiom_sub>"


-- | translate a list of conjunctive casl formulas to a subrule of TRS
conj_sub :: [FORMULA f] -> String
conj_sub fs =
  if length fs == 2 then ("and(" ++ (axiom_sub $ head fs) ++ "," ++
                                   (axiom_sub $ last fs) ++ ")")
  else ("and(" ++ (axiom_sub $ head fs) ++ "," ++
                  (conj_sub $ tail fs) ++ ")")


-- | translate a list of disjunctive casl formulas to a subrule of TRS
disj_sub :: [FORMULA f] -> String
disj_sub fs =
  if length fs == 2 then ("or(" ++ (axiom_sub $ head fs) ++ "," ++
                                  (axiom_sub $ last fs) ++ ")")
  else ("or(" ++ (axiom_sub $ head fs) ++ "," ++
                 (disj_sub $ tail fs) ++ ")")


-- | It translates the conditional casl axiom(implication or equivalence) 
--   to TRS-rule: "A -> B | C -> D, ...". After "|" follow the conditions.
--   All conditional axioms are handled specially in Terme Rewrite Systems.
impli_equiv_trs :: FORMULA f -> String
impli_equiv_trs f = 
  case (quanti f) of
    Implication _ _ _ _ -> impli_str f
    Equivalence _ _ _ -> equiv_str f
    _ -> error "CASL.CCC.TerminationProof.<impli_equiv_trs2>"


-- | implication is handled specially as a conditional formula,
--   it translates a implication to TRS-rule
impli_str :: FORMULA f -> String
impli_str f =
  case (quanti f) of
    Implication f1 f2 False _ -> (axiom_sub (quanti f2)) ++ " -> true | " ++
                                 (axiom_sub (quanti f1)) ++ " -> true\n"
    Implication (Predication predS1 ts1 _) f1 _ _ ->
        case (quanti f1) of
          Conjunction _ _ ->
              ((axiom_sub (quanti f1)) ++ " -> true | " ++ 
              (predSymName predS1) ++ "(" ++ (terms_pa ts1) ++ ") -> true\n")
          Negation (Conjunction _ _) _ ->
              ((axiom_sub (quanti f1)) ++ " -> false | " ++ 
              (predSymName predS1) ++ "(" ++ (terms_pa ts1) ++ ") -> true\n")
          Disjunction _ _ ->
              ((axiom_sub (quanti f1)) ++ " -> true | " ++ 
              (predSymName predS1) ++ "(" ++ (terms_pa ts1) ++ ") -> true\n")
          Negation (Disjunction _ _) _ ->
              ((axiom_sub (quanti f1)) ++ " -> false | " ++ 
              (predSymName predS1) ++ "(" ++ (terms_pa ts1) ++ ") -> true\n")
          Predication predS2 ts2 _ ->
              ((predSymName predS2) ++ "(" ++ (terms_pa ts2) ++ 
              ") -> true | " ++ (predSymName predS1) ++ "(" ++ 
              (terms_pa ts1) ++ ") -> true\n")
          Negation (Predication predS2 ts2 _) _ ->
              ((predSymName predS2) ++ "(" ++ (terms_pa ts2) ++ 
              ") -> false | " ++ (predSymName predS1) ++ "(" ++ 
              (terms_pa ts1) ++ ") -> true\n")
          Strong_equation t1 t2 _ ->
              ("eq(" ++ (term_trs t1) ++ "," ++ (term_trs t2) ++ 
              ") -> true | " ++ (predSymName predS1) ++ "(" ++ 
              (terms_pa ts1) ++ ") -> true\n")
          Negation (Strong_equation t1 t2 _) _ ->
              ("eq(" ++ (term_trs t1) ++ "," ++ (term_trs t2) ++ 
              ") -> false | " ++ (predSymName predS1) ++ "(" ++ 
              (terms_pa ts1) ++ ") -> true\n")
          Equivalence (Predication predS2 ts2 _) f2 _ ->
              case (quanti f2) of
                Conjunction _ _ ->
                    ((axiom_sub (quanti f2)) ++ " -> true | " ++ 
                    (predSymName predS1) ++ "(" ++ 
                    (terms_pa ts1) ++ ") -> true, " ++ 
                    (predSymName predS2) ++ "(" ++ 
                    (terms_pa ts2) ++ ") -> true\n")
                Negation (Conjunction _ _) _ ->
                    ((axiom_sub (quanti f2)) ++ " -> false | " ++ 
                    (predSymName predS1) ++ "(" ++ 
                    (terms_pa ts1) ++ ") -> true, " ++ 
                    (predSymName predS2) ++ "(" ++ 
                    (terms_pa ts2) ++ ") -> true\n")
                Disjunction _ _ ->
                    ((axiom_sub (quanti f2)) ++ " -> true | " ++ 
                    (predSymName predS1) ++ "(" ++ 
                    (terms_pa ts1) ++ ") -> true, " ++ 
                    (predSymName predS2) ++ "(" ++ 
                    (terms_pa ts2) ++ ") -> true\n")
                Negation (Disjunction _ _) _ ->
                    ((axiom_sub (quanti f2)) ++ " -> false | " ++ 
                    (predSymName predS1) ++ "(" ++ 
                    (terms_pa ts1) ++ ") -> true, " ++ 
                    (predSymName predS2) ++ "(" ++ 
                    (terms_pa ts2) ++ ") -> true\n")
                Predication predS3 ts3 _ ->
                    ((predSymName predS3) ++ "(" ++ (terms_pa ts3) ++ 
                    ") -> true | "++
                    (predSymName predS1) ++ "(" ++ (terms_pa ts1) ++ 
                    ") -> true, " ++ 
                    (predSymName predS2) ++ "(" ++ (terms_pa ts2) ++
                    ") -> true\n")
                Negation (Predication predS3 ts3 _) _ ->
                    ((predSymName predS3) ++ "(" ++ (terms_pa ts3) ++ 
                    ") -> false | "++
                    (predSymName predS1) ++ "(" ++ (terms_pa ts1) ++ 
                    ") -> true, " ++ 
                    (predSymName predS2) ++ "(" ++ (terms_pa ts2) ++
                    ") -> true\n")
                Strong_equation t1 t2 _ ->
                    ("eq(" ++ (term_trs t1) ++ "," ++ (term_trs t2) ++ 
                    ") -> true | " ++
                    (predSymName predS1) ++ "(" ++ (terms_pa ts1) ++
                    ") -> true, " ++ 
                    (predSymName predS2) ++ "(" ++ (terms_pa ts2) ++
                    ") -> true\n")
                Negation (Strong_equation t1 t2 _) _ ->
                    ("eq(" ++ (term_trs t1) ++ "," ++ (term_trs t2) ++ 
                    ") -> false | " ++
                    (predSymName predS1) ++ "(" ++ (terms_pa ts1) ++
                    ") -> true, " ++ 
                    (predSymName predS2) ++ "(" ++ (terms_pa ts2) ++
                    ") -> true\n")
                _ -> error "CASL.CCC.TerminationProof.<impli_str_p_eq_p>"
          Equivalence (Strong_equation t1 t2 _) f2 _ ->
              case (quanti f2) of
                Conjunction _ _ ->
                    ((axiom_sub (quanti f2)) ++ " -> true | " ++ 
                    (predSymName predS1) ++ "(" ++ (terms_pa ts1) ++ 
                    ") -> true, " ++ (term_trs t1) ++ " -> " ++ 
                    (term_trs t2) ++ "\n" ++
                    "eq(" ++ (term_trs t1) ++ "," ++ (term_trs t2) ++
                    ") -> true | " ++ 
                    (predSymName predS1) ++ "(" ++ (terms_pa ts1) ++ 
                    ") -> true, " ++ (axiom_sub (quanti f2)) ++
                    " -> true\n")
                Negation (Conjunction _ _) _ ->
                    ((axiom_sub (quanti f2)) ++ " -> false | " ++ 
                    (predSymName predS1) ++ "(" ++ (terms_pa ts1) ++ 
                    ") -> true, " ++ (term_trs t1) ++ " -> " ++ 
                    (term_trs t2) ++ "\n" ++
                    "eq(" ++ (term_trs t1) ++ "," ++ (term_trs t2) ++
                    ") -> true | " ++ 
                    (predSymName predS1) ++ "(" ++ (terms_pa ts1) ++ 
                    ") -> true, " ++ (axiom_sub (quanti f2)) ++
                    " -> false\n")
                Disjunction _ _ ->
                    ((axiom_sub (quanti f2)) ++ " -> true | " ++ 
                    (predSymName predS1) ++ "(" ++ (terms_pa ts1) ++ 
                    ") -> true, " ++ (term_trs t1) ++ " -> " ++
                    (term_trs t2) ++ "\n" ++
                    "eq(" ++ (term_trs t1) ++ "," ++ (term_trs t2) ++
                    ") -> true | " ++ 
                    (predSymName predS1) ++ "(" ++ (terms_pa ts1) ++ 
                    ") -> true, " ++ (axiom_sub (quanti f2)) ++
                    " -> true\n")
                Negation (Disjunction _ _) _ ->
                    ((axiom_sub (quanti f2)) ++ " -> false | " ++ 
                    (predSymName predS1) ++ "(" ++ (terms_pa ts1) ++ 
                    ") -> true, " ++ (term_trs t1) ++ " -> " ++ 
                    (term_trs t2) ++ "\n" ++ 
                    "eq(" ++ (term_trs t1) ++ "," ++ (term_trs t2) ++
                    ") -> true | " ++ 
                    (predSymName predS1) ++ "(" ++ (terms_pa ts1) ++ 
                    ") -> true, " ++ (axiom_sub (quanti f2)) ++
                    " -> false\n")
                Predication predS2 ts2 _ ->
                    ((predSymName predS2) ++ "(" ++ (terms_pa ts2) ++ 
                    ") -> true | " ++ 
                    (predSymName predS1) ++ "(" ++ (terms_pa ts1) ++ 
                    ") -> true, " ++ (term_trs t1) ++ " -> " ++
                    (term_trs t2) ++ "\n" ++ 
                    "eq(" ++ (term_trs t1) ++ "," ++ (term_trs t2) ++
                    ") -> true | " ++ 
                    (predSymName predS1) ++ "(" ++ (terms_pa ts1) ++ 
                    ") -> true, " ++ (predSymName predS2) ++ "(" ++
                    (terms_pa ts2) ++ ") -> true\n")
                Negation (Predication predS2 ts2 _) _ ->
                    ((predSymName predS2) ++ "(" ++ (terms_pa ts2) ++ 
                    ") -> false | " ++ 
                    (predSymName predS1) ++ "(" ++ (terms_pa ts1) ++ 
                    ") -> true, " ++ (term_trs t1) ++ " -> " ++
                    (term_trs t2) ++ "\n" ++ 
                    "eq(" ++ (term_trs t1) ++ "," ++ (term_trs t2) ++
                    ") -> true | " ++ 
                    (predSymName predS1) ++ "(" ++ (terms_pa ts1) ++ 
                    ") -> true, " ++ (predSymName predS2) ++ "(" ++
                    (terms_pa ts2) ++ ") -> false\n")
                Strong_equation t3 t4 _ ->
                    ("eq(" ++ (term_trs t3) ++ "," ++ (term_trs t4) ++ 
                    ") -> true | " ++ (predSymName predS1) ++ "(" ++ 
                    (terms_pa ts1) ++ ") -> true, " ++ (term_trs t1) ++ 
                    " -> " ++ (term_trs t2) ++ "\n" ++
                    "eq(" ++ (term_trs t1) ++ "," ++ (term_trs t2) ++ 
                    ") -> true | " ++ (predSymName predS1) ++ "(" ++ 
                    (terms_pa ts1) ++ ") -> true, " ++ (term_trs t3) ++ 
                    " -> " ++ (term_trs t4) ++ "\n")
                Negation (Strong_equation t3 t4 _) _ ->
                    ("eq(" ++ (term_trs t3) ++ "," ++ (term_trs t4) ++ 
                    ") -> false | " ++ (predSymName predS1) ++ "(" ++ 
                    (terms_pa ts1) ++ ") -> true, " ++ (term_trs t1) ++ 
                    " -> " ++ (term_trs t2) ++ "\n" ++
                    "eq(" ++ (term_trs t1) ++ "," ++ (term_trs t2) ++ 
                    ") -> true | " ++ (predSymName predS1) ++ "(" ++ 
                    (terms_pa ts1) ++ ") -> true, eq(" ++ (term_trs t3) ++ 
                    "," ++ (term_trs t4) ++ ") -> false\n")
                Existl_equation t3 t4 _ ->
                    ("eq(" ++ (term_trs t3) ++ "," ++ (term_trs t4) ++ 
                    ") -> true | " ++ (predSymName predS1) ++ "(" ++ 
                    (terms_pa ts1) ++ ") -> true, " ++ (term_trs t1) ++ 
                    " -> " ++ (term_trs t2) ++ "\n" ++
                    "eq(" ++ (term_trs t1) ++ "," ++ (term_trs t2) ++ 
                    ") -> true | " ++ (predSymName predS1) ++ "(" ++ 
                    (terms_pa ts1) ++ ") -> true, " ++ (term_trs t3) ++ 
                    " -> " ++ (term_trs t4) ++ "\n")
                Negation (Existl_equation t3 t4 _) _ ->
                    ("eq(" ++ (term_trs t3) ++ "," ++ (term_trs t4) ++ 
                    ") -> false | " ++ (predSymName predS1) ++ "(" ++ 
                    (terms_pa ts1) ++ ") -> true, " ++ (term_trs t1) ++ 
                    " -> " ++ (term_trs t2) ++ "\n" ++
                    "eq(" ++ (term_trs t1) ++ "," ++ (term_trs t2) ++ 
                    ") -> true | " ++ (predSymName predS1) ++ "(" ++ 
                    (terms_pa ts1) ++ ") -> true, eq(" ++ (term_trs t3) ++ 
                    "," ++ (term_trs t4) ++ ") -> false\n")                   
                _ -> error "CASL.CCC.TerminationProof.<impli_str_p_eq_str>"
          _ -> error "CASL.CCC.TerminationProof.<impli_str_p>"
    Implication (Strong_equation t1 t2 _) f1 _ _ ->
        case (quanti f1) of
          Conjunction _ _ ->
              ((axiom_sub (quanti f1)) ++ " -> true | " ++ 
              (term_trs t1) ++ " -> " ++ (term_trs t2) ++ "\n")
          Negation (Conjunction _ _) _ ->
              ((axiom_sub (quanti f1)) ++ " -> false | " ++ 
              (term_trs t1) ++ " -> " ++ (term_trs t2) ++ "\n")
          Disjunction _ _ ->
              ((axiom_sub (quanti f1)) ++ " -> true | " ++ 
              (term_trs t1) ++ " -> " ++ (term_trs t2) ++ "\n")
          Negation (Disjunction _ _) _ ->
              ((axiom_sub (quanti f1)) ++ " -> false | " ++ 
              (term_trs t1) ++ " -> " ++ (term_trs t2) ++ "\n")
          Predication predS ts _ ->
              ((predSymName predS) ++ "(" ++ (terms_pa ts) ++ ") -> true | " ++
              (term_trs t1) ++ " -> " ++ (term_trs t2) ++ "\n")
          Negation (Predication predS ts _) _ ->
              ((predSymName predS) ++ "(" ++ (terms_pa ts) ++ ") -> false | "++
              (term_trs t1) ++ " -> " ++ (term_trs t2) ++ "\n")
          Strong_equation t3 t4 _ ->
              ("eq(" ++ (term_trs t3) ++ "," ++ (term_trs t4) ++ 
              ") -> true | " ++
              (term_trs t1) ++ " -> " ++ (term_trs t2) ++ "\n")
          Negation (Strong_equation t3 t4 _) _ ->
              ("eq(" ++ (term_trs t3) ++ "," ++ (term_trs t4) ++ 
              ") -> false | " ++
              (term_trs t1) ++ " -> " ++ (term_trs t2) ++ "\n")
          Equivalence (Predication predS1 ts1 _) f2 _->
              case (quanti f2) of
                Conjunction _ _ ->
                    ((axiom_sub (quanti f2)) ++ " -> true | " ++ 
                    (term_trs t1) ++ " -> " ++ (term_trs t2) ++ ", " ++
                    (predSymName predS1) ++ "(" ++ (terms_pa ts1) ++ 
                    ") -> true\n")
                Negation (Conjunction _ _) _ ->
                    ((axiom_sub (quanti f2)) ++ " -> false | " ++ 
                    (term_trs t1) ++ " -> " ++ (term_trs t2) ++ ", " ++
                    (predSymName predS1) ++ "(" ++ (terms_pa ts1) ++ 
                    ") -> true\n")
                Disjunction _ _ ->
                    ((axiom_sub (quanti f2)) ++ " -> true | " ++ 
                    (term_trs t1) ++ " -> " ++ (term_trs t2) ++ ", " ++
                    (predSymName predS1) ++ "(" ++ (terms_pa ts1) ++ 
                    ") -> true\n")
                Negation (Disjunction _ _) _ ->
                    ((axiom_sub (quanti f2)) ++ " -> false | " ++ 
                    (term_trs t1) ++ " -> " ++ (term_trs t2) ++ ", " ++
                    (predSymName predS1) ++ "(" ++ (terms_pa ts1) ++ 
                    ") -> true\n")
                Predication predS2 ts2 _ ->
                    ((predSymName predS2) ++ "(" ++ (terms_pa ts2) ++ 
                    ") -> true | " ++
                    (term_trs t1) ++ " -> " ++ (term_trs t2) ++ ", " ++
                    (predSymName predS1) ++ "(" ++ (terms_pa ts1) ++ 
                    ") -> true\n")
                Negation (Predication predS2 ts2 _) _ ->
                    ((predSymName predS2) ++ "(" ++ (terms_pa ts2) ++ 
                    ") -> false | " ++
                    (term_trs t1) ++ " -> " ++ (term_trs t2) ++ ", " ++
                    (predSymName predS1) ++ "(" ++ (terms_pa ts1) ++ 
                    ") -> true\n")
                Strong_equation t3 t4 _ ->
                    ("eq(" ++  (term_trs t3) ++ "," ++ (term_trs t4) ++
                    ") -> true | " ++
                    (term_trs t1) ++ " -> " ++ (term_trs t2) ++ ", " ++
                    (predSymName predS1) ++ "(" ++ (terms_pa ts1) ++
                    ") -> true\n")
                Negation (Strong_equation t3 t4 _) _ ->
                    ("eq(" ++  (term_trs t3) ++ "," ++ (term_trs t4) ++
                    ") -> false | " ++
                    (term_trs t1) ++ " -> " ++ (term_trs t2) ++ ", " ++
                    (predSymName predS1) ++ "(" ++ (terms_pa ts1) ++
                    ") -> true\n")
                _ -> error "CASL.CCC.TerminationProof.<impli_str_str_eq_p>"
          Equivalence (Strong_equation t3 t4 _) f2 _->
              case (quanti f2) of
                Conjunction _ _ ->
                    ((axiom_sub (quanti f2)) ++ " -> true | " ++ 
                    (term_trs t1) ++ " -> " ++ (term_trs t2) ++ ", " ++
                    (term_trs t3) ++ " -> " ++ (term_trs t4) ++ "\n" ++
                    "eq(" ++ (term_trs t3) ++ "," ++ (term_trs t4) ++
                    ") -> true | " ++
                    (term_trs t1) ++ " -> " ++ (term_trs t2) ++ ", " ++
                    (axiom_sub (quanti f2)) ++ " -> true\n")
                Negation (Conjunction _ _) _ ->
                    ((axiom_sub (quanti f2)) ++ " -> false | " ++ 
                    (term_trs t1) ++ " -> " ++ (term_trs t2) ++ ", " ++
                    (term_trs t3) ++ " -> " ++ (term_trs t4) ++ "\n" ++
                    "eq(" ++ (term_trs t3) ++ "," ++ (term_trs t4) ++
                    ") -> true | " ++
                    (term_trs t1) ++ " -> " ++ (term_trs t2) ++ ", " ++
                    (axiom_sub (quanti f2)) ++ " -> false\n")
                Disjunction _ _ ->
                    ((axiom_sub (quanti f2)) ++ " -> true | " ++ 
                    (term_trs t1) ++ " -> " ++ (term_trs t2) ++ ", " ++
                    (term_trs t3) ++ " -> " ++ (term_trs t4) ++ "\n" ++
                    "eq(" ++ (term_trs t3) ++ "," ++ (term_trs t4) ++
                    ") -> true | " ++
                    (term_trs t1) ++ " -> " ++ (term_trs t2) ++ ", " ++
                    (axiom_sub (quanti f2)) ++ " -> true\n")
                Negation (Disjunction _ _) _ ->
                    ((axiom_sub (quanti f2)) ++ " -> false | " ++ 
                    (term_trs t1) ++ " -> " ++ (term_trs t2) ++ ", " ++
                    (term_trs t3) ++ " -> " ++ (term_trs t4) ++ "\n" ++
                    "eq(" ++ (term_trs t3) ++ "," ++ (term_trs t4) ++
                    ") -> true | " ++
                    (term_trs t1) ++ " -> " ++ (term_trs t2) ++ ", " ++
                    (axiom_sub (quanti f2)) ++ " -> false\n")
                Predication predS ts _ ->
                    ((predSymName predS) ++ "(" ++ (terms_pa ts) ++ 
                    ") -> true | " ++
                    (term_trs t1) ++ " -> " ++ (term_trs t2) ++ ", " ++
                    (term_trs t3) ++ " -> " ++ (term_trs t4) ++ "\n" ++
                    "eq(" ++ (term_trs t3) ++ "," ++ (term_trs t4) ++ 
                    ") -> true | " ++
                    (term_trs t1) ++ " -> " ++ (term_trs t2) ++ ", " ++
                    (predSymName predS) ++ "(" ++ (terms_pa ts) ++ 
                    ") -> true\n")
                Negation (Predication predS ts _) _ ->
                    ((predSymName predS) ++ "(" ++ (terms_pa ts) ++ 
                    ") -> false | " ++
                    (term_trs t1) ++ " -> " ++ (term_trs t2) ++ ", " ++
                    (term_trs t3) ++ " -> " ++ (term_trs t4) ++ "\n" ++
                    "eq(" ++ (term_trs t3) ++ "," ++ (term_trs t4) ++ 
                    ") -> true | " ++
                    (term_trs t1) ++ " -> " ++ (term_trs t2) ++ ", " ++
                    (predSymName predS) ++ "(" ++ (terms_pa ts) ++ 
                    ") -> false\n")
                Strong_equation t5 t6 _ ->
                    ("eq(" ++ (term_trs t5) ++ "," ++ (term_trs t6) ++ 
                    ") -> true | " ++
                    (term_trs t1) ++ " -> " ++ (term_trs t2) ++ ", " ++
                    (term_trs t3) ++ " -> " ++ (term_trs t4) ++ "\n" ++
                    "eq(" ++ (term_trs t3) ++ "," ++ (term_trs t4) ++ 
                    ") -> true | " ++
                    (term_trs t1) ++ " -> " ++ (term_trs t2) ++ ", " ++
                    (term_trs t5) ++ " -> " ++ (term_trs t6) ++ "\n")
                Negation (Strong_equation t5 t6 _) _ ->
                    ("eq(" ++ (term_trs t5) ++ "," ++ (term_trs t6) ++ 
                    ") -> false | " ++
                    (term_trs t1) ++ " -> " ++ (term_trs t2) ++ ", " ++
                    (term_trs t3) ++ " -> " ++ (term_trs t4) ++ "\n" ++
                    "eq(" ++ (term_trs t3) ++ "," ++ (term_trs t4) ++ 
                    ") -> true | " ++
                    (term_trs t1) ++ " -> " ++ (term_trs t2) ++ ", eq(" ++
                    (term_trs t5) ++ "," ++ (term_trs t6) ++ ") -> false\n")
                _ -> error "CASL.CCC.TerminationProof.<impli_str_str_eq_str>"
          _ -> error "CASL.CCC.TerminationProof.<impli_str_str>"
    _ -> error "CASL.CCC.TerminationProof.<impli_str>"


-- | Equivalence is handled specially as a conditional formula,
--   it translates a equivalence to TRS-rule 
equiv_str :: FORMULA f -> String
equiv_str f =
  case (quanti f) of
    Equivalence (Predication predS1 ts1 _) f1 _ ->
        case (quanti f1) of
          Conjunction _ _ ->
              ((axiom_sub (quanti f1)) ++ " -> true | " ++ 
              (predSymName predS1) ++ "(" ++ (terms_pa ts1) ++ ") -> true\n")
          Negation (Conjunction _ _) _ ->
              ((axiom_sub (quanti f1)) ++ " -> false | " ++ 
              (predSymName predS1) ++ "(" ++ (terms_pa ts1) ++ ") -> true\n")
          Disjunction _ _ ->
              ((axiom_sub (quanti f1)) ++ " -> true | " ++ 
              (predSymName predS1) ++ "(" ++ (terms_pa ts1) ++ ") -> true\n")
          Negation (Disjunction _ _) _ ->
              ((axiom_sub (quanti f1)) ++ " -> false | " ++ 
              (predSymName predS1) ++ "(" ++ (terms_pa ts1) ++ ") -> true\n")
          Predication predS2 ts2 _ ->
              ((predSymName predS2) ++ "(" ++ (terms_pa ts2) ++ 
              ") -> true | " ++
              (predSymName predS1) ++ "(" ++ (terms_pa ts1) ++ ") -> true\n")
          Negation (Predication predS2 ts2 _) _ ->
              ((predSymName predS2) ++ "(" ++ (terms_pa ts2) ++ 
              ") -> false | " ++
              (predSymName predS1) ++ "(" ++ (terms_pa ts1) ++ ") -> true\n")
          Strong_equation t1 t2 _ -> 
              ("eq(" ++ (term_trs t1) ++ "," ++ (term_trs t2) ++ 
              ") -> true | " ++
              (predSymName predS1) ++ "(" ++ (terms_pa ts1) ++ ") -> true\n")
          Negation (Strong_equation t1 t2 _) _ ->
              ("eq(" ++ (term_trs t1) ++ "," ++ (term_trs t2) ++ 
              ") -> false | " ++
              (predSymName predS1) ++ "(" ++ (terms_pa ts1) ++ ") -> true\n")
          _ -> error "CASL.CCC.TerminationProof.<equiv_str_pred>"
    Equivalence (Strong_equation t1 t2 _) f1 _ ->
        case (quanti f1) of
          Conjunction _ _ ->
              ((axiom_sub (quanti f1)) ++ " -> true | " ++ 
              (term_trs t1) ++ " -> " ++ (term_trs t2) ++ "\n" ++
              "eq(" ++ (term_trs t1) ++ "," ++ (term_trs t2) ++ 
              ") -> true | " ++
              (axiom_sub (quanti f1)) ++ " -> true\n")
          Negation (Conjunction _ _) _ ->
              ((axiom_sub (quanti f1)) ++ " -> false | " ++ 
              (term_trs t1) ++ " -> " ++ (term_trs t2) ++ "\n" ++
              "eq(" ++ (term_trs t1) ++ "," ++ (term_trs t2) ++ 
              ") -> true | " ++
              (axiom_sub (quanti f1)) ++ " -> false\n")
          Disjunction _ _ ->
              ((axiom_sub (quanti f1)) ++ " -> true | " ++ 
              (term_trs t1) ++ " -> " ++ (term_trs t2) ++ "\n" ++
              "eq(" ++ (term_trs t1) ++ "," ++ (term_trs t2) ++ 
              ") -> true | " ++
              (axiom_sub (quanti f1)) ++ " -> true\n")
          Negation (Disjunction _ _) _ ->
              ((axiom_sub (quanti f1)) ++ " -> false | " ++ 
              (term_trs t1) ++ " -> " ++ (term_trs t2) ++ "\n" ++
              "eq(" ++ (term_trs t1) ++ "," ++ (term_trs t2) ++ 
              ") -> true | " ++
              (axiom_sub (quanti f1)) ++ " -> false\n")
          Predication predS ts _ ->
              ((predSymName predS) ++ "(" ++ (terms_pa ts) ++ 
              ") -> true | " ++
              (term_trs t1) ++ " -> " ++ (term_trs t2) ++ "\n" ++
              "eq(" ++ (term_trs t1) ++ "," ++ (term_trs t2) ++ 
              ") -> true | " ++
              (predSymName predS) ++ "(" ++ (terms_pa ts) ++ ") -> true\n")
          Negation (Predication predS ts _) _ ->
              ((predSymName predS) ++ "(" ++ (terms_pa ts) ++ 
              ") -> false | " ++
              (term_trs t1) ++ " -> " ++ (term_trs t2) ++ "\n" ++
              "eq(" ++ (term_trs t1) ++ "," ++ (term_trs t2) ++ 
              ") -> true | " ++
              (predSymName predS) ++ "(" ++ (terms_pa ts) ++ ") -> false\n")
          Strong_equation t3 t4 _ ->
              ("eq(" ++ (term_trs t3) ++ "," ++ (term_trs t4) ++ 
              ") -> true | " ++
              (term_trs t1) ++ " -> " ++ (term_trs t2) ++ "\n" ++
              "eq(" ++ (term_trs t1) ++ "," ++ (term_trs t2) ++ 
              ") -> true | " ++
              (term_trs t3) ++ " -> " ++ (term_trs t4) ++ "\n")
          Negation (Strong_equation t3 t4 _) _ ->
              ("eq(" ++ (term_trs t3) ++ "," ++ (term_trs t4) ++ 
              ") -> false | " ++
              (term_trs t1) ++ " -> " ++ (term_trs t2) ++ "\n" ++
              "eq(" ++ (term_trs t1) ++ "," ++ (term_trs t2) ++ 
              ") -> true | eq(" ++
              (term_trs t3) ++ "," ++ (term_trs t4) ++ ") -> false\n")
          _ -> error "CASL.CCC.TerminationProof.<equiv_str_str>"
    _ -> error "CASL.CCC.TerminationProof.<equiv_str>"

    