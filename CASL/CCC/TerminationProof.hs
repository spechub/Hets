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
-- import Common.DocUtils
import CASL.CCC.TermFormula
import Common.Id
import Common.Utils (getEnvDef)
import System.Cmd
import System.IO.Unsafe
import System.Directory
-- import Debug.Trace
import Data.List (nub)

{-
   Automatic termination proof
   using AProVE, see http://aprove.informatik.rwth-aachen.de/

   interface to AProVE system, using system
   translate CASL signature to AProVE Input Language,
   CASL formulas to AProVE term rewrite systems(TRS),
   see http://aprove.informatik.rwth-aachen.de/help/html/in/trs.html

   if a equation system is terminal, then it is computable.
-}

terminationProof :: Eq f => [FORMULA f] -> [(TERM f,FORMULA f)] -> Maybe Bool
terminationProof fs dms
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
        | otherwise =
            axiomTrs (tail axs) (str ++ (axiom_trs (head axs) dms) ++ "\n")
    axhead = "(RULES\neq(t,t) -> true\n" ++
             "eq(_,_) -> false\n" ++
             "when_else(t1,true,t2) -> t1\n" ++
             "when_else(t1,false,t2) -> t2\n"
    c_vars = ("(VAR t t1 t2 " ++ (varsStr (allVar $ map varOfAxiom $
                                fs) "") ++ ")\n")
    c_axms = axhead ++ (axiomTrs fs "") ++ ")\n"
    ipath = "/Input.trs"
    opath = "/Result.txt"
    proof = unsafePerformIO (do
                tmpDir <- getTemporaryDirectory
                writeFile (tmpDir ++ ipath) (c_vars ++ c_axms)
                aprovePath <- getEnvDef "HETS_APROVE"
                  "CASL/Termination/AProVE.jar"
                system ("java -jar " ++ aprovePath ++ " -u cli -m " ++
                        "wst -p plain " ++ tmpDir ++
                        ipath ++ " | head -n 1 > " ++ tmpDir ++ opath)
                res <- readFile (tmpDir ++ opath)
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
    Qual_var var _ _ -> tokStr var
    Application (Op_name opn) [] _ ->
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


-- | translate a casl axiom to TRS-rule:
--   a rule without condition is represented by "A -> B" in
--   Term Rewrite Systems; if there are some conditions, then
--   follow the conditions after the symbol "|".
--   For example : "A -> B | C -> D, E -> F, ..."
axiom_trs :: (Eq f) => FORMULA f -> [(TERM f,FORMULA f)] -> String
axiom_trs f doms =
  case (quanti f) of
    Quantification _ _ f' _ -> axiom_trs f' doms
    Conjunction fs _ ->
        conj_sub fs ++ " -> true"
    Disjunction fs _ ->
        disj_sub fs ++ " -> true"
    Implication f1 f2 _ _ ->
        case f2 of
          Equivalence f3 f4 _ ->
              (axiom_trs f3 doms) ++  " | " ++
              (axiom_trs f1 doms) ++ ", " ++
              (axiom_trs f4 doms)
          _ ->
              case f1 of
                Definedness t _ ->
                    let dm = filter (\d -> sameOps_App t (fst d)) doms
                        phi = snd $ head dm
                        te = fst $ head dm
                        p1 = arguOfTerm te
                        p2 = arguOfTerm t
                        st = zip p2 p1
                    in if not $ null dm
                       then (axiom_trs f2 doms) ++ " | " ++
                            (axiom_trs (substiF st phi) doms)
                       else (axiom_trs f2 doms) ++
                            " | def(" ++ (term_trs t) ++ ") -> open"
                _ -> (axiom_trs f2 doms) ++  " | " ++
                     (axiom_trs f1 doms)
    Equivalence f1 f2 _ ->
         (axiom_trs f1 doms) ++ " | " ++
         (axiom_trs f2 doms)
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
        "def(" ++ (term_trs t) ++ ") -> open"
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
        "def(" ++ (term_trs t) ++ ")"
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
