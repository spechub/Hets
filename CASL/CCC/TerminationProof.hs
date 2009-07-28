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
import Common.Utils (getEnvDef, nubOrd)
import System.Cmd
import System.IO.Unsafe
import System.Directory
-- import Debug.Trace

{-
   Automatic termination proof
   using AProVE, see http://aprove.informatik.rwth-aachen.de/

   interface to AProVE system, using system
   translate CASL signature to AProVE Input Language,
   CASL formulas to AProVE term rewrite systems(TRS),
   see http://aprove.informatik.rwth-aachen.de/help/html/in/trs.html

   if a equation system is terminal, then it is computable.
-}

terminationProof :: Ord f => [FORMULA f] -> [(TERM f,FORMULA f)] -> Maybe Bool
terminationProof fs dms
    | null fs            = Just True
    | proof == "YES\n"   = Just True
    | proof == "MAYBE\n" = Nothing
    | proof == "NO\n"    = Just False
    | otherwise          = Nothing
    where
    allVar = nubOrd . concat
    varsStr vars str
        | null vars = str
        | otherwise = if null str then varsStr (tail vars) (tokStr $ head vars)
                      else varsStr (tail vars) (str ++ " " ++tokStr (head vars))
    axiomTrs axs str
     | null axs = str
     | otherwise = axiomTrs (tail axs) (str ++ axiom2TRS (head axs) dms ++ "\n")
    axhead = "(RULES\neq(t,t) -> true\n" ++
             "eq(_,_) -> false\n" ++
             "when_else(t1,true,t2) -> t1\n" ++
             "when_else(t1,false,t2) -> t2\n"
    c_vars = "(VAR t t1 t2 " ++ varsStr (allVar $ map varOfAxiom fs) "" ++ ")\n"
    c_axms = axhead ++ axiomTrs fs "" ++ ")\n"
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
                readFile (tmpDir ++ opath))


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
term2TRS :: TERM f -> String
term2TRS t =
  case (term t) of
    Qual_var var _ _ -> tokStr var
    Application (Op_name opn) [] _ -> idStr opn
    Application (Qual_op_name opn _ _) ts _ ->
        if null ts then idStr opn
        else idStr opn ++ "(" ++ termsPA ts ++")"
    Sorted_term t' _ _ -> term2TRS t'
    Cast t' _ _ -> term2TRS t'
    Conditional t1 f t2 _ ->
        "when_else(" ++ term2TRS t1 ++ "," ++ t_f_str f ++ "," ++
          term2TRS t2 ++ ")"
    _ -> error "CASL.CCC.TerminationProof.<term2TRS>"
  where t_f_str f = case f of                     --  condition of a term
                    Strong_equation t1 t2 _ ->
                        "eq(" ++ term2TRS t1 ++ "," ++ term2TRS t2 ++ ")"
                    Predication ps ts _ ->
                        if null ts then predSymName ps
                        else predSymName ps ++ "(" ++ termsPA ts ++ ")"
                    _ -> error "CASL.CCC.TerminationProof.<term2TRS_cond>"


-- | translate a list of casl terms to the patterns of a term in TRS
termsPA :: [TERM f] -> String
termsPA ts =
    if null ts then "" else tail $ concatMap ((\ s -> ',':s) . term2TRS) ts


-- | translate a casl axiom to TRS-rule:
--   a rule without condition is represented by "A -> B" in
--   Term Rewrite Systems; if there are some conditions, then
--   follow the conditions after the symbol "|".
--   For example : "A -> B | C -> D, E -> F, ..."
axiom2TRS :: (Eq f) => FORMULA f -> [(TERM f,FORMULA f)] -> String
axiom2TRS f doms =
  case (quanti f) of
    Quantification _ _ f' _ -> axiom2TRS f' doms
    Conjunction fs _ -> conjSub fs doms ++ " -> true"
    Disjunction fs _ -> disjSub fs doms ++ " -> true"
    Implication f1 f2 _ _ ->
        case f2 of
          Equivalence f3 f4 _ ->
              axiom2TRS f3 doms ++  " | " ++ axiom2TRS f1 doms ++ ", " ++
              axiom2TRS f4 doms
          _ ->
              case f1 of
                Definedness t _ ->
                    let dm = filter (sameOps_App t . fst) doms
                        phi = snd $ head dm
                        te = fst $ head dm
                        p1 = arguOfTerm te
                        p2 = arguOfTerm t
                        st = zip p2 p1
                    in if not $ null dm
                       then axiom2TRS f2 doms ++ " | " ++
                            axiom2TRS (substiF st phi) doms
                       else axiom2TRS f2 doms ++
                            " | def(" ++ term2TRS t ++ ") -> open"
                _ -> axiom2TRS f2 doms ++  " | " ++ axiom2TRS f1 doms
    Equivalence f1 f2 _ -> axiom2TRS f1 doms ++ " | " ++ axiom2TRS f2 doms
    Negation f' _ ->
        case f' of
          Conjunction fs _ -> conjSub fs doms ++ " -> false"
          Disjunction fs _ -> disjSub fs doms ++ " -> false"
          Predication p_s ts _ ->
              if null ts
              then predSymName p_s ++ " -> false"
              else predSymName p_s ++ "(" ++ termsPA ts ++ ") -> false"
          Strong_equation t1 t2 _ ->
              "eq(" ++ term2TRS t1 ++ "," ++ term2TRS t2 ++ ") -> false"
          Definedness t _ -> term2TRS t ++ " -> undefined"
          _ -> error "CASL.CCC.TerminationProof.<axiom2TRS_Negation>"
    Predication p_s ts _ ->
        if null ts then predSymName p_s ++ " -> true"
        else predSymName p_s ++ "(" ++ termsPA ts ++ ") -> true"
    Definedness t _ -> "def(" ++ term2TRS t ++ ") -> open"
    Strong_equation t1 t2 _ ->
        case t2 of
          Conditional tt1 ff tt2 _ ->
              term2TRS t1 ++ " -> " ++ term2TRS tt1 ++ " | " ++
              axiomSub ff doms ++ " -> true\n" ++
              term2TRS t1 ++ " -> " ++ term2TRS tt2 ++ " | " ++
              axiomSub ff doms ++ " -> false"
          _ -> if isApp t1
               then term2TRS t1 ++ " -> " ++ term2TRS t2
               else "eq(" ++ term2TRS t1 ++ "," ++ term2TRS t2 ++
                    ") -> true"
    True_atom _ -> "true -> true"
    False_atom _ -> "false -> false"
    _ -> error "CASL.CCC.TerminationProof.<axiom2TRS>"


-- | translate a casl axiom(without conditions) to a subrule of TRS,
-- | the handling of an implication in a subrule is yet to be correctly defined.
axiomSub :: (Eq f) => FORMULA f -> [(TERM f,FORMULA f)] -> String
axiomSub f doms =
  case (quanti f) of
    Quantification _ _ f' _ -> axiomSub f' doms
    Conjunction fs _ -> conjSub fs doms
    Disjunction fs _ -> disjSub fs doms
    Negation f' _ ->
        case f' of
          Conjunction fs _ -> "not(" ++ conjSub fs doms ++ ")"
          Disjunction fs _ -> "not(" ++ disjSub fs doms ++ ")"
          Predication p_s ts _ ->
              if null ts then "not(" ++ predSymName p_s ++ ")"
              else "not(" ++ predSymName p_s ++ "(" ++ termsPA ts ++ "))"
          Strong_equation t1 t2 _ ->
              "not(eq(" ++ term2TRS t1 ++ "," ++ term2TRS t2 ++ "))"
          _ -> error "CASL.CCC.TerminationProof.str_substr.<Negation>"
    True_atom _ -> "true"
    False_atom _ -> "false"
    Predication p_s ts _ ->
        if null ts then predSymName p_s
        else predSymName p_s ++ "(" ++ termsPA ts ++ ")"
    Definedness t _ -> "def(" ++ term2TRS t ++ ")"
    Strong_equation t1 t2 _ -> "eq(" ++ term2TRS t1 ++ "," ++ term2TRS t2 ++ ")"
    i@(Implication _ _ _ _) -> axiom2TRS i doms
    _ -> error "CASL.CCC.TerminationProof.axiomSub.<axiomSub>"


-- | translate a list of conjunctive casl formulas to a subrule of TRS
conjSub :: (Eq f) => [FORMULA f] -> [(TERM f,FORMULA f)] -> String
conjSub fs doms =
  if length fs == 2 then "and(" ++ axiomSub (head fs) doms ++ "," ++
                                   axiomSub (last fs) doms ++ ")"
  else "and(" ++ axiomSub (head fs) doms ++ "," ++ conjSub (tail fs) doms ++ ")"


-- | translate a list of disjunctive casl formulas to a subrule of TRS
disjSub :: (Eq f) => [FORMULA f] -> [(TERM f,FORMULA f)] -> String
disjSub fs doms =
  if length fs == 2 then "or(" ++ axiomSub (head fs) doms ++ "," ++
                                  axiomSub (last fs) doms ++ ")"
  else "or(" ++ axiomSub (head fs) doms ++ "," ++ disjSub (tail fs) doms ++ ")"
