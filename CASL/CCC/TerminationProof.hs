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

module CASL.CCC.TerminationProof (terminationProof) where

import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.ToDoc
import CASL.CCC.TermFormula
  ( unsortedTerm
  , quanti
  , arguOfTerm
  , substiF
  , sameOpsApp)

import Common.DocUtils
import Common.Id
import Common.ProofUtils
import Common.Result
import Common.Utils

import Control.Monad

import System.Process
import System.Directory

import Data.List (intercalate, partition)
import Data.Maybe
import Data.Function (on)

import qualified Data.Map as Map

{-
   Automatic termination proof
   using AProVE, see http://aprove.informatik.rwth-aachen.de/

   interface to AProVE system, using system
   translate CASL signature to AProVE Input Language,
   CASL formulas to AProVE term rewrite systems(TRS),
   see http://aprove.informatik.rwth-aachen.de/help/html/in/trs.html

   if a equation system is terminal, then it is computable.
-}

terminationProof :: (FormExtension f, Ord f) => Sign f e -> [FORMULA f]
  -> [(TERM f, FORMULA f)] -> IO (Maybe Bool, String)
terminationProof sig fs dms =
  if null fs then return (Just True, "no formulas") else do
  let
    axhead =
      [ "(RULES"
      , "eq(t,t) -> true"
      , "eq(_,_) -> false"
      , "and(true,t) -> t"
      , "and(false,t) -> false"
      , "or(true,t) -> true"
      , "or(false,t) -> t"
      , "implies(false,t) -> true"
      , "implies(true,t) -> t"
      , "equiv(t,t) -> true"
      , "equiv(_,_) -> false"
      , "not(true) -> false"
      , "not(false) -> true"
      , "when_else(t1,true,t2) -> t1"
      , "when_else(t1,false,t2) -> t2" ]
    c_vars = "(VAR t t1 t2 "
      ++ unwords (map transToken . nubOrd $ concatMap varOfAxiom fs) ++ ")"
    (rs, ls) = partition (isJust . maybeResult) $ map (axiom2TRS sig dms) fs
    c_axms = axhead ++ map (fromJust . maybeResult) rs ++ [")"]
  if null ls then do
      tmpFile <- getTempFile (unlines $ c_vars : c_axms) "Input.trs"
      aprovePath <- getEnvDef "HETS_APROVE" "CASL/Termination/AProVE.jar"
      (_, proof, _) <- readProcessWithExitCode "java"
        ("-ea" : "-jar" : aprovePath : words "-u cli -m wst -p plain"
         ++ [tmpFile]) ""
      removeFile tmpFile
      return (case words proof of
        "YES" : _ -> Just True
        "NO" : _ -> Just False
        _ -> Nothing, proof)
    else return (Nothing, unlines . map show $ concatMap diags ls)

-- | extract all variables of a axiom
varOfAxiom :: FORMULA f -> [VAR]
varOfAxiom f = case f of
    Quantification _ vd _ _ ->
        concatMap (\ (Var_decl vs _ _) -> vs) vd
    _ -> []

keywords :: [String]
keywords = ["eq", "or", "implies", "equiv", "when_else"]
  -- others are CASL keywords
  ++ ["CONTEXTSENSITIVE", "EQUATIONS", "INNERMOST", "RULES", "STRATEGY"
     , "THEORY", "VAR"]

transStringAux :: String -> String
transStringAux = concatMap (\ c -> Map.findWithDefault [c] c charMap)

transString :: String -> String
transString s = let t = transStringAux s in
  if elem t keywords then '_' : t else t

transToken :: Token -> String
transToken = transString . tokStr

transId :: Id -> ShowS
transId (Id ts cs _) =
    showSepList id (showString . transToken) ts .
    if null cs then id else
    showString "{" . showSepList (showString "-") transId cs
    . showString "}"

-- | translate id to string
idStr :: Id -> String
idStr i = transId i ""

-- | get the name of a operation symbol
opSymName :: OP_SYMB -> String
opSymName = idStr . opSymbName

-- | get the name of a predicate symbol
predSymName :: PRED_SYMB -> String
predSymName = idStr . predSymbName

-- | create a predicate application
predAppl :: (Monad m, FormExtension f) => PRED_SYMB -> [TERM f] -> m String
predAppl p = liftM (predSymName p ++) . termsPA

-- | apply function string to argument string with brackets
apply :: String -> String -> String
apply f a = f ++ "(" ++ a ++ ")"

-- | create a binary application
applyBin :: String -> String -> String -> String
applyBin o t1 t2 = apply o $ t1 ++ "," ++ t2

-- | translate a casl term to a term of TRS(Terme Rewrite Systems)
term2TRS :: (Monad m, FormExtension f) => TERM f -> m String
term2TRS t = case unsortedTerm t of
  Qual_var var _ _ -> return $ tokStr var
  Application o ts _ -> liftM (opSymName o ++) $ termsPA ts
  Conditional t1 f t2 _ -> do
    b1 <- term2TRS t1
    c <- axiomSub f
    b2 <- term2TRS t2
    return $ apply "when_else" $ b1 ++ "," ++ c ++ "," ++ b2
  _ -> fail "CASL.CCC.TerminationProof.<term2TRS>"

-- | translate a list of casl terms to the patterns of a term in TRS
termsPA :: (Monad m, FormExtension f) => [TERM f] -> m String
termsPA ts = if null ts then return "" else
    liftM (apply "" . intercalate ",") $ mapM term2TRS ts

{- | translate a casl axiom to TRS-rule:
a rule without condition is represented by "A -> B" in
Term Rewrite Systems; if there are some conditions, then
follow the conditions after the symbol "|".
For example : "A -> B | C -> D, E -> F, ..." -}
axiom2TRS :: (FormExtension f, Eq f, Monad m) => Sign f e
  -> [(TERM f, FORMULA f)] -> FORMULA f -> m String
axiom2TRS sig doms f = case quanti f of
  Relation f1 c f2 _ | c /= Equivalence -> do
    a1 <- axiom2Cond f1
    t2 <- axiom2Rule f2
    case f2 of
      Relation f3 Equivalence f4 _ -> do
        a3 <- axiom2Rule f3
        a4 <- axiom2Cond f4
        return $ a3 ++ " | " ++ a1 ++ ", " ++ a4
      _ -> case f1 of
        Definedness t _ -> case filter (sameOpsApp sig t . fst) doms of
          [] -> return $ t2 ++ " | " ++ a1
          (te, phi) : _ -> do
            let st = on zip arguOfTerm t te
            sc <- axiom2Cond (substiF st phi)
            return $ t2 ++ " | " ++ sc
        _ -> return $ t2 ++ " | " ++ a1
  Relation f1 Equivalence f2 _ -> do
    r1 <- axiom2Rule f1
    c2 <- axiom2Cond f2
    return $ r1 ++ " | " ++ c2
  _ -> axiom2Rule f

axiom2Cond :: (Monad m, FormExtension f) => FORMULA f -> m String
axiom2Cond = axiom2Rule

axiom2Rule :: (Monad m, FormExtension f) => FORMULA f -> m String
axiom2Rule f = case quanti f of
  Negation f' _ -> case f' of
    Quantification {} ->
      fail "CASL.CCC.TerminationProof.<axiom2TRS_Negation>"
    Definedness t _ -> liftM (++ " -> undefined") $ term2TRS t
    _ -> liftM (++ " -> false") $ axiomSub f'
  Definedness t _ -> liftM ((++ " -> open") . apply "def") $ term2TRS t
  Equation t1 Strong t2 _ -> do
    e1 <- term2TRS t1
    case t2 of
      Conditional tt1 ff tt2 _ -> do
        c <- axiomSub ff
        b1 <- term2TRS tt1
        b2 <- term2TRS tt2
        return $ e1 ++ " -> " ++ b1 ++ " | "
          ++ c ++ " -> true\n"
          ++ e1 ++ " -> " ++ b2 ++ " | "
          ++ c ++ " -> false"
      _ -> do
        e2 <- term2TRS t2
        return $ if isApp t1 then e1 ++ " -> " ++ e2 else
          applyBin "eq" e1 e2 ++ " -> true"
  Atom False _ -> return "false -> false"
  _ -> liftM (++ " -> true") $ axiomSub f

-- | check whether it is a application term
isApp :: TERM t -> Bool
isApp t = case unsortedTerm t of
  Application {} -> True
  _ -> False

-- | translate a casl axiom (without conditions) to a term of TRS,
axiomSub :: (Monad m, FormExtension f) => FORMULA f -> m String
axiomSub f = case quanti f of
  Junction j fs@(_ : _) _ -> do
    as <- mapM axiomSub fs
    return $ foldr1 (applyBin $ if j == Con then "and" else "or") as
  Negation f' _ -> liftM (apply "not") $ axiomSub f'
  Atom b _ -> return $ if b then "true" else "false"
  Predication p_s ts _ -> predAppl p_s ts
  Definedness t _ -> liftM (apply "def") $ term2TRS t
  Equation t1 _ t2 _ -> do -- support any equation
    e1 <- term2TRS t1
    e2 <- term2TRS t2
    return $ applyBin "eq" e1 e2
  Relation f1 c f2 _ -> do
    s1 <- axiomSub f1
    s2 <- axiomSub f2
    return $ applyBin (if c == Equivalence then "equiv" else "implies") s1 s2
  _ -> fail $ "CASL.CCC.TerminationProof.axiomSub.<axiomSub> " ++ showDoc f ""
