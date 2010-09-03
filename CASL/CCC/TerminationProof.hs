{- |
Module      :  $Header$
Description :  termination proofs for equation systems, using AProVE
Copyright   :  (c) Mingyi Liu and Till Mossakowski and Uni Bremen 2004-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  xinga@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Termination proofs for equation systems, using AProVE
-}

module CASL.CCC.TerminationProof
  ( terminationProof
  , opSymName
  , predSymName
  ) where

import CASL.AS_Basic_CASL
import CASL.CCC.TermFormula
  ( term
  , quanti
  , isApp
  , arguOfTerm
  , varOfAxiom
  , idStr
  , substiF
  , sameOpsApp)

import Common.Id (Token (tokStr))
import Common.Utils

import System.Process
import System.Directory

import Data.List (intercalate)

{-
   Automatic termination proof
   using AProVE, see http://aprove.informatik.rwth-aachen.de/

   interface to AProVE system, using system
   translate CASL signature to AProVE Input Language,
   CASL formulas to AProVE term rewrite systems(TRS),
   see http://aprove.informatik.rwth-aachen.de/help/html/in/trs.html

   if a equation system is terminal, then it is computable.
-}

terminationProof :: Ord f => [FORMULA f] -> [(TERM f, FORMULA f)]
  -> IO (Maybe Bool)
terminationProof fs dms = if null fs then return $ Just True else do
  let
    allVar = nubOrd . concat
    varsStr vars str = case vars of
      [] -> str
      h : t -> varsStr t $
        (if null str then "" else str ++ " ") ++ tokStr h
    axiomTrs axs str = case axs of
      [] -> str
      h : t -> axiomTrs t $ str ++ axiom2TRS h dms ++ "\n"
    axhead = "(RULES\neq(t,t) -> true\n" ++
             "eq(_,_) -> false\n" ++
             "when_else(t1,true,t2) -> t1\n" ++
             "when_else(t1,false,t2) -> t2\n"
    c_vars = "(VAR t t1 t2 " ++ varsStr (allVar $ map varOfAxiom fs) "" ++ ")\n"
    c_axms = axhead ++ axiomTrs fs "" ++ ")\n"
  tmpFile <- getTempFile (c_vars ++ c_axms) "Input.trs"
  aprovePath <- getEnvDef "HETS_APROVE"
                  "CASL/Termination/AProVE.jar"
  (_, proof, _) <- readProcessWithExitCode "java"
    ("-jar" : aprovePath : words "-u cli -m wst -p plain" ++ [tmpFile]) ""
  removeFile tmpFile
  return $ case words proof of
    "YES" : _ -> Just True
    "NO" : _ -> Just False
    _ -> Nothing

-- | get the name of a operation symbol
opSymName :: OP_SYMB -> String
opSymName = idStr . opSymbName

-- | get the name of a predicate symbol
predSymName :: PRED_SYMB -> String
predSymName = idStr . predSymbName

-- | create a predicate application
predAppl :: PRED_SYMB -> [TERM f] -> String
predAppl p ts = predSymName p
  ++ if null ts then "" else apply "" $ termsPA ts

-- | apply function string to argument string with brackets
apply :: String -> String -> String
apply f a = f ++ "(" ++ a ++ ")"

-- | create an eq application
applyEq :: TERM f -> TERM f -> String
applyEq t1 t2 = apply "eq" $ term2TRS t1 ++ "," ++ term2TRS t2

-- | translate a casl term to a term of TRS(Terme Rewrite Systems)
term2TRS :: TERM f -> String
term2TRS t = case term t of
    Qual_var var _ _ -> tokStr var
    Application o ts _ -> opSymName o ++ termsPA ts
    Sorted_term t' _ _ -> term2TRS t'
    Cast t' _ _ -> term2TRS t'
    Conditional t1 f t2 _ ->
        apply "when_else" $ term2TRS t1 ++ "," ++ t_f_str f ++ "," ++
              term2TRS t2
    _ -> error "CASL.CCC.TerminationProof.<term2TRS>"
  where t_f_str f = case f of                     -- condition of a term
                    Strong_equation t1 t2 _ -> applyEq t1 t2
                    Predication ps ts _ -> predAppl ps ts
                    _ -> error "CASL.CCC.TerminationProof.<term2TRS_cond>"

-- | translate a list of casl terms to the patterns of a term in TRS
termsPA :: [TERM f] -> String
termsPA ts = if null ts then "" else
   apply "" . intercalate "," $ map term2TRS ts

{- | translate a casl axiom to TRS-rule:
a rule without condition is represented by "A -> B" in
Term Rewrite Systems; if there are some conditions, then
follow the conditions after the symbol "|".
For example : "A -> B | C -> D, E -> F, ..." -}
axiom2TRS :: Eq f => FORMULA f -> [(TERM f, FORMULA f)] -> String
axiom2TRS f doms =
  case quanti f of
    Quantification _ _ f' _ -> axiom2TRS f' doms
    Implication f1 f2 _ _ ->
        case f2 of
          Equivalence f3 f4 _ ->
              axiom2TRS f3 doms ++ " | " ++ axiom2TRS f1 doms ++ ", " ++
              axiom2TRS f4 doms
          _ ->
              case f1 of
                Definedness t _ ->
                    let dm = filter (sameOpsApp t . fst) doms
                        phi = snd $ head dm
                        te = fst $ head dm
                        p1 = arguOfTerm te
                        p2 = arguOfTerm t
                        st = zip p2 p1
                    in if not $ null dm
                       then axiom2TRS f2 doms ++ " | " ++
                            axiom2TRS (substiF st phi) doms
                       else axiom2TRS f2 doms ++
                            " | " ++ apply "def" (term2TRS t) ++ " -> open"
                _ -> axiom2TRS f2 doms ++ " | " ++ axiom2TRS f1 doms
    Equivalence f1 f2 _ -> axiom2TRS f1 doms ++ " | " ++ axiom2TRS f2 doms
    Negation f' _ ->
        case f' of
          Quantification {} ->
              error "CASL.CCC.TerminationProof.<axiom2TRS_Negation>"
          Definedness t _ -> term2TRS t ++ " -> undefined"
          _ -> axiomSub f' doms ++ " -> false"
    Definedness t _ -> apply "def" (term2TRS t) ++ " -> open"
    Strong_equation t1 t2 _ ->
        case t2 of
          Conditional tt1 ff tt2 _ ->
              term2TRS t1 ++ " -> " ++ term2TRS tt1 ++ " | " ++
              axiomSub ff doms ++ " -> true\n" ++
              term2TRS t1 ++ " -> " ++ term2TRS tt2 ++ " | " ++
              axiomSub ff doms ++ " -> false"
          _ -> if isApp t1
               then term2TRS t1 ++ " -> " ++ term2TRS t2
               else applyEq t1 t2 ++ " -> true"
    False_atom _ -> "false -> false"
    _ -> axiomSub f doms ++ " -> true"


{- | translate a casl axiom(without conditions) to a subrule of TRS,
the handling of an implication in a subrule is yet to be correctly defined. -}
axiomSub :: Eq f => FORMULA f -> [(TERM f, FORMULA f)] -> String
axiomSub f doms =
  case quanti f of
    Quantification _ _ f' _ -> axiomSub f' doms
    Conjunction fs _ -> conjSub fs doms
    Disjunction fs _ -> disjSub fs doms
    Negation f' _ -> apply "not" $ axiomSub f' doms
    True_atom _ -> "true"
    False_atom _ -> "false"
    Predication p_s ts _ -> predAppl p_s ts
    Definedness t _ -> apply "def" $ term2TRS t
    Strong_equation t1 t2 _ -> applyEq t1 t2
    i@(Implication _ _ _ _) -> axiom2TRS i doms
    _ -> error "CASL.CCC.TerminationProof.axiomSub.<axiomSub>"


-- | translate a list of conjunctive casl formulas to a subrule of TRS
conjSub :: Eq f => [FORMULA f] -> [(TERM f, FORMULA f)] -> String
conjSub fs doms = foldr1 (\ x r -> apply "and" $ x ++ "," ++ r)
  $ map (`axiomSub` doms) fs

-- | translate a list of disjunctive casl formulas to a subrule of TRS
disjSub :: Eq f => [FORMULA f] -> [(TERM f, FORMULA f)] -> String
disjSub fs doms = foldr1 (\ x r -> apply "or" $ x ++ "," ++ r)
  $ map (`axiomSub` doms) fs
