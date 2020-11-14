{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./Comorphisms/SoftFOL2CommonLogic.hs
Description :  Coding of SoftFOL into CommonLogic
Copyright   :  (c) Eugen Kuksa and Uni Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  eugenk@informatik.uni-bremen.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

The translating comorphism from SoftFOL to CommonLogic.
-}

module Comorphisms.SoftFOL2CommonLogic
    (
     SoftFOL2CommonLogic (..)
    )
    where

import Data.Maybe (maybeToList)

import Common.ProofTree
import Common.Id
import Common.Result
import Common.Utils (concatMapM)
import qualified Common.AS_Annotation as AS_Anno
import qualified Common.DefaultMorphism as DefaultMorphism
import qualified Common.Lib.Rel as Rel

import Logic.Logic
import Logic.Comorphism

import qualified Data.HashSet as Set
import qualified Data.HashMap.Strict as Map

-- SoftFOL
import qualified SoftFOL.Logic_SoftFOL as FOLLogic
import qualified SoftFOL.Sign as FOLSign

-- CommonLogic
import CommonLogic.AS_CommonLogic
import qualified CommonLogic.Logic_CommonLogic as ClLogic
import qualified CommonLogic.Sign as ClSign
import qualified CommonLogic.Symbol as ClSymbol
import qualified CommonLogic.Morphism as ClMor
import qualified CommonLogic.Sublogic as ClSL

-- | lid of the morphism
data SoftFOL2CommonLogic = SoftFOL2CommonLogic deriving Show

instance Language SoftFOL2CommonLogic where
  language_name SoftFOL2CommonLogic = "SoftFOL2CommonLogic"

instance Comorphism SoftFOL2CommonLogic
    FOLLogic.SoftFOL         -- lid domain
    ()                       -- sublogics codomain
    [FOLSign.TPTP]          -- Basic spec domain
    FOLSign.Sentence         -- sentence domain
    ()                       -- symbol items domain
    ()                       -- symbol map items domain
    FOLSign.Sign             -- signature domain
    FOLSign.SoftFOLMorphism  -- morphism domain
    FOLSign.SFSymbol         -- symbol domain
    ()                       -- rawsymbol domain
    ProofTree                -- proof tree codomain
    ClLogic.CommonLogic      -- lid domain
    ClSL.CommonLogicSL       -- sublogics codomain
    BASIC_SPEC               -- Basic spec domain
    TEXT_META                -- sentence domain
    SYMB_ITEMS               -- symb_items
    SYMB_MAP_ITEMS           -- symbol map items domain
    ClSign.Sign              -- signature domain
    ClMor.Morphism           -- morphism domain
    ClSymbol.Symbol          -- symbol domain
    ClSymbol.Symbol          -- rawsymbol domain
    ProofTree                -- proof tree codomain
    where
      sourceLogic SoftFOL2CommonLogic = FOLLogic.SoftFOL
      sourceSublogic SoftFOL2CommonLogic = ()
      targetLogic SoftFOL2CommonLogic = ClLogic.CommonLogic
      mapSublogic SoftFOL2CommonLogic = Just . mapSub
      map_theory SoftFOL2CommonLogic = mapTheory
      map_sentence SoftFOL2CommonLogic = mapSentence
      map_morphism SoftFOL2CommonLogic = mapMor

mapSub :: () -> ClSL.CommonLogicSL
mapSub _ = ClSL.folsl

mapMor :: FOLSign.SoftFOLMorphism -> Result ClMor.Morphism
mapMor mor =
  let src = mapSign $ DefaultMorphism.domOfDefaultMorphism mor
      tgt = mapSign $ DefaultMorphism.codOfDefaultMorphism mor
      pmp = Map.empty
  in return $ ClMor.Morphism src tgt pmp

mapSentence :: FOLSign.Sign -> FOLSign.Sentence -> Result TEXT_META
mapSentence = translate

mapSign :: FOLSign.Sign -> ClSign.Sign
mapSign sig =
  let items = Set.map (\ t -> mkId [t]) $ Set.fromList $ concat
                                [ Map.keys $ FOLSign.sortMap sig
                                , Map.keys $ FOLSign.funcMap sig
                                , Map.keys $ FOLSign.predMap sig
                                ]
  in ClSign.emptySig { ClSign.discourseNames = items }

-- | translates SoftFOL-theories to CL-theories keeping their names
mapTheory :: (FOLSign.Sign, [AS_Anno.Named FOLSign.Sentence])
             -> Result (ClSign.Sign, [AS_Anno.Named TEXT_META])
mapTheory (srcSign, srcFormulas) = do
  trans_fs <- mapM (transSnd . senAndName) srcFormulas
  return (mapSign srcSign, signToTexts srcSign
       ++ map (uncurry AS_Anno.makeNamed) trans_fs)
  where senAndName :: AS_Anno.Named FOLSign.Sentence -> (String, FOLSign.Sentence)
        senAndName f = (AS_Anno.senAttr f, AS_Anno.sentence f)
        transSnd :: (String, FOLSign.Sentence) -> Result (String, TEXT_META)
        transSnd (s, f) = do
          tm <- translate srcSign f
          return (s, tm)

-- translates a SoftFOL-theory to a CL-Text
translate :: FOLSign.Sign -> FOLSign.Sentence -> Result TEXT_META
translate s f = do
  sen <- trmToSen s f
  return $ emptyTextMeta { getText = Text [Sentence sen] nullRange }

signToTexts :: FOLSign.Sign -> [AS_Anno.Named TEXT_META]
signToTexts srcSign =
  let sr = sortRelText $ Rel.toMap $ FOLSign.sortRel srcSign
      fm = funcMapText $ FOLSign.funcMap srcSign
      pm = predMapText $ FOLSign.predMap srcSign
  in concat
      [ map (AS_Anno.makeNamed sortRelTrS) (maybeToList sr)
      , map (AS_Anno.makeNamed funcMapTrS) (maybeToList fm)
      , map (AS_Anno.makeNamed predMapTrS) (maybeToList pm)
      ]

-- creates one-sentence-phrases: forall x. (subSort x) => (superSort x)
sortRelText :: Map.HashMap FOLSign.SPIdentifier (Set.HashSet FOLSign.SPIdentifier)
                -> Maybe TEXT_META
sortRelText m =
  let ps = Map.foldrWithKey (\ subSrt set phrs ->
        Set.foldr (\ superSrt phrs2 ->
            Sentence (Quant_sent Universal [Name xName]
                      (Bool_sent (BinOp Implication
                                  (predicateNames subSrt [xName])
                                  (predicateNames superSrt [xName])
                                 ) nullRange) nullRange)
            : phrs2) [] set
        ++ phrs) [] m
  in if null ps
        then Nothing
        else Just $ emptyTextMeta { getText = Named_text (mkSimpleId sortRelTrS)
                                                (Text ps nullRange) nullRange
                                  }

typesWithIndv :: [Token] -> [(Token, NAME)] -- (type, individual)
typesWithIndv args =
  foldr (\ (a, i) resArg -> (a, indv a i) : resArg) [] $ zip args [0 ..]

{- creates one-sentence-phrases:
forall x y z. (if (and (T1 x) (T2 y) (T3 z)) (T4 f[x,y,z])) -}
funcMapText :: Map.HashMap Token (Set.HashSet ([Token], Token)) -> Maybe TEXT_META
funcMapText m =
  let ps = Map.foldrWithKey (\ f set phrs ->
          Set.foldr (\ (args, res) phrs2 ->
            let argsAndNames = typesWithIndv args
            in Sentence (
                  if null args
                  then predicateNames res [f]
                  else
                    Quant_sent Universal
                                (map (Name . snd) argsAndNames) (
                      Bool_sent (BinOp Implication
                          (Bool_sent (Junction Conjunction $
                              map (\ (p, x) -> predicateNames p [x]) argsAndNames
                            ) nullRange)
                          (Atom_sent (Atom
                              (Name_term res)
                              [Term_seq $ Funct_term (Name_term f) (
                                  map (Term_seq . Name_term . snd) argsAndNames
                                ) nullRange]
                            ) nullRange)
                        ) nullRange
                      ) nullRange)
            : phrs2) [] set
          ++ phrs) [] m
  in if null ps
        then Nothing
        else Just $ emptyTextMeta { getText = Named_text (mkSimpleId funcMapTrS)
                                                (Text ps nullRange) nullRange
                                  }

{- creates one-sentence-phrases:
forall x y z. (P[x,y,z]) => (and (T1 x) (T2 y) (T3 z)) -}
predMapText :: Map.HashMap Token (Set.HashSet [Token]) -> Maybe TEXT_META
predMapText m =
  let ps = Map.foldrWithKey (\ prd set phrs ->
          Set.foldr (\ args phrs2 ->
            let argsAndNames = typesWithIndv args
            in Sentence (Quant_sent Universal
                                      (map (Name . snd) argsAndNames) (
                    Bool_sent (BinOp Implication
                        (predicateNames prd (map snd argsAndNames))
                        (Bool_sent (Junction Conjunction $
                            map (\ (p, x) -> predicateNames p [x]) argsAndNames
                          ) nullRange)
                      ) nullRange
                    ) nullRange)
            : phrs2) [] set
          ++ phrs) [] m
  in if null ps
        then Nothing
        else Just $ emptyTextMeta { getText = Named_text
                                                (mkSimpleId predMapTrS)
                                                (Text ps nullRange)
                                                nullRange
                                  }

trmToSen :: FOLSign.Sign -> FOLSign.SPTerm -> Result SENTENCE
trmToSen s t = case t of
  FOLSign.SPQuantTerm qsym vl f -> quantTrm s qsym vl f
  FOLSign.SPComplexTerm sym args -> case sym of
    FOLSign.SPEqual -> case args of
        [x, y] -> toEquation (x, y)
        l@(_ : _ : _) -> do
            eqs <- mapM toEquation $ zip l $ tail l
            return $ Bool_sent (Junction Conjunction eqs) nullRange
        x -> fail $ "equation needs at least two arguments, but found: " ++ show x
    FOLSign.SPTrue -> return clTrue
    FOLSign.SPFalse -> return clFalse
    FOLSign.SPOr -> do
        sens <- mapM (trmToSen s) args
        return $ Bool_sent (Junction Disjunction sens) nullRange
    FOLSign.SPAnd -> do
        sens <- mapM (trmToSen s) args
        return $ Bool_sent (Junction Conjunction sens) nullRange
    FOLSign.SPNot -> case args of
        [x] -> do
          sen <- trmToSen s x
          return $ Bool_sent (Negation sen) nullRange
        _ -> fail $
              "negation can only be applied to a single argument, but found: "
              ++ show t
    FOLSign.SPImplies -> case args of
        [x, y] -> do
            sen1 <- trmToSen s x
            sen2 <- trmToSen s y
            return $ Bool_sent (BinOp Implication sen1 sen2) nullRange
        _ -> fail $
              "implication can only be applied to two arguments, but found: "
              ++ show t
    FOLSign.SPImplied -> case args of
        [x, y] -> do
            sen1 <- trmToSen s x
            sen2 <- trmToSen s y
            return $ Bool_sent (BinOp Implication sen2 sen1) nullRange
        _ -> fail $
              "implication can only be applied to two arguments, but found: "
              ++ show t
    FOLSign.SPEquiv -> case args of
        [x, y] -> do
            sen1 <- trmToSen s x
            sen2 <- trmToSen s y
            return $ Bool_sent (BinOp Biconditional sen1 sen2) nullRange
        _ -> fail $
              "equivalence can only be applied to two arguments, but found: "
              ++ show t
    _ -> predicateSPTerms (symToTerm sym) args

-- | converts SPEquation to a CL-Equation
toEquation :: (FOLSign.SPTerm, FOLSign.SPTerm) -> Result SENTENCE
toEquation (x, y) = do
  trmx <- trmToTerm x
  trmy <- trmToTerm y
  return $ Atom_sent (Equation trmx trmy) nullRange

predicateSPTerms :: TERM -> [FOLSign.SPTerm] -> Result SENTENCE
predicateSPTerms t args = do
  tseqs <- mapM trmToTermSeq args
  return $ Atom_sent (Atom t tseqs) nullRange

predicateNames :: NAME -> [NAME] -> SENTENCE
predicateNames p xs =
  Atom_sent (Atom (Name_term p) (map (Term_seq . Name_term) xs)) nullRange

predicateTerm :: NAME -> TERM -> SENTENCE
predicateTerm p xs = Atom_sent (Atom (Name_term p) [Term_seq xs]) nullRange

{- Converts a quantified FOL-term to a CL-Quant_sent. Quantifier arguments
contain only the inner-most arguments  of the SoftFOL Quantifier in order to
convert sentences like
@forall s(Y1), t(u(Y2)) .  Y1 /= Y2@
to
@forall Y1, Y2 . S(Y1) & T(u(Y2)) & U(Y2) => Y1 /= Y2@
where S, T and U are the types that Y1, u(Y2) and Y2 must have
in order to apply functions/predicates s, t and u to them (defined in
funcMap and predMap). -}
quantTrm :: FOLSign.Sign -> FOLSign.SPQuantSym
            -> [FOLSign.SPTerm] -> FOLSign.SPTerm -> Result SENTENCE
quantTrm sig qsymm vs f = do
  let functions_quant = filter (not . isNullary) vs
  let trans_vs = concatMap trmToNameSeq vs
  trans_f <- if null functions_quant
             then trmToSen sig f
             else do
               sen1 <- typeSentence sig functions_quant
               sen2 <- trmToSen sig f
               return $ Bool_sent (BinOp Implication sen1 sen2) nullRange
  quantifier <- case qsymm of
        FOLSign.SPForall -> return Universal
        FOLSign.SPExists -> return Existential
        _ -> fail "custom quantifiers not allowed"
  return $ Quant_sent quantifier trans_vs trans_f nullRange

typeSentence :: FOLSign.Sign -> [FOLSign.SPTerm] -> Result SENTENCE
typeSentence sig vs = case vs of
  [] -> return clTrue
  [v] -> typeSentence1 sig v      -- v = f(x,y,z)
  _ -> do
      sens <- mapM (typeSentence1 sig) vs
      return $ Bool_sent (Junction Conjunction sens) nullRange

typeSentence1 :: FOLSign.Sign -> FOLSign.SPTerm -> Result SENTENCE
typeSentence1 sig v = case v of
  FOLSign.SPComplexTerm _ [] ->
    fail "bug (typeSentence1): nullary functions should not occur here"
  FOLSign.SPComplexTerm sym args -> typeSentenceGetTypes sig (symToName sym) args
  FOLSign.SPQuantTerm {} ->
    fail "quantification not allowed in bound variable list"

typeSentenceGetTypes :: FOLSign.Sign -> FOLSign.SPIdentifier -> [FOLSign.SPTerm]
                        -> Result SENTENCE
typeSentenceGetTypes sig symN args =
  case Map.lookup symN $ FOLSign.funcMap sig of
    Nothing -> case Map.lookup symN $ FOLSign.predMap sig of
      Nothing -> case Map.lookup symN $ FOLSign.sortMap sig of
        Nothing -> fail $ "symbol has no type: " ++ show symN
        Just _ -> typeSentencesSort args symN
      Just ts -> typeSentencesDisjPred sig args $ Set.elems ts
    Just ts -> typeSentencesDisjFunc sig args $ Set.elems ts

typeSentencesSort :: [FOLSign.SPTerm] -> FOLSign.SPIdentifier
                     -> Result SENTENCE
typeSentencesSort args srt = case args of
  [] -> fail $ "no arguments for sort " ++ show srt
  [arg] -> do
      funtrm <- trmToFunctTrm arg
      return $ predicateTerm srt funtrm
  _ -> do
      sens <- mapM (\ arg -> do
                     funtrm <- trmToFunctTrm arg
                     return $ predicateTerm srt funtrm
                   ) args
      return $ Bool_sent (Junction Conjunction sens) nullRange

typeSentencesDisjPred :: FOLSign.Sign -> [FOLSign.SPTerm]
                         -> [[FOLSign.SPIdentifier]]
                         -> Result SENTENCE
typeSentencesDisjPred sig args typeSet = case typeSet of
  [t] -> tsdp1 t
  _ -> do
    sens <- mapM tsdp1 typeSet
    return $ Bool_sent (Junction Disjunction sens) nullRange
  where tsdp1 :: [FOLSign.SPIdentifier] -> Result SENTENCE
        tsdp1 t = do
          sens <- mapM (\ (arg, argType) -> case arg of
              FOLSign.SPComplexTerm _ [] ->
                return $ predicateNames argType [trmToName arg]
              FOLSign.SPComplexTerm _ _ ->
                typeSentence1 sig arg
              FOLSign.SPQuantTerm {} ->
                fail "quantification not allowed in quantifier-argument list"
            ) $ zip args t
          return $ Bool_sent (Junction Conjunction sens) nullRange

typeSentencesDisjFunc :: FOLSign.Sign -> [FOLSign.SPTerm]
                         -> [([FOLSign.SPIdentifier], FOLSign.SPIdentifier)]
                         -> Result SENTENCE
typeSentencesDisjFunc sig args typeSet = case typeSet of
  [t] -> tsdf1 t
  _ -> do
      sens <- mapM tsdf1 typeSet
      return $ Bool_sent (Junction Disjunction sens) nullRange
  where tsdf1 :: ([FOLSign.SPIdentifier], FOLSign.SPIdentifier) -> Result SENTENCE
        tsdf1 (t, resType) = do
          sens <- concatMapM (\ (arg, argType) -> case arg of
              FOLSign.SPComplexTerm _ [] ->
                return [predicateNames argType [trmToName arg]]
              FOLSign.SPComplexTerm _ _ -> do
                funtrm <- trmToFunctTrm arg
                typsen <- typeSentence1 sig arg
                return [predicateTerm resType funtrm, typsen]
              FOLSign.SPQuantTerm {} ->
                fail "quantification not allowed in quantifier-argument list"
            ) $ zip args t
          return $ Bool_sent (Junction Conjunction sens) nullRange

trmToName :: FOLSign.SPTerm -> NAME
trmToName t = case t of
  FOLSign.SPComplexTerm sym _ -> symToName sym
  x -> error $ "quantification not convertible to a name: " ++ show x

{- converts an @SPTerm@ to @[NAME_OR_SEQMARK]@ as an argument for a quantifier
using only the inner-most arguments -}
trmToNameSeq :: FOLSign.SPTerm -> [NAME_OR_SEQMARK]
trmToNameSeq t = case t of
  FOLSign.SPComplexTerm sym [] -> [Name $ symToName sym]
  FOLSign.SPComplexTerm _ args -> concatMap trmToNameSeq args
  FOLSign.SPQuantTerm {} ->
      error "quantification not allowed in quantifier-argument list"

-- converts an SPTerm to a TERM, i.e. for the arguments of an equation
trmToTerm :: FOLSign.SPTerm -> Result TERM
trmToTerm t = case t of
  FOLSign.SPQuantTerm {} -> fail "quantification not allowed for a term"
  FOLSign.SPComplexTerm _ [] -> return $ Name_term $ trmToName t
  FOLSign.SPComplexTerm _ _ -> trmToFunctTrm t

-- Converts an SPTerm to TERM_SEQ as an argument for a quantifier
trmToTermSeq :: FOLSign.SPTerm -> Result TERM_SEQ
trmToTermSeq t = case t of
  FOLSign.SPComplexTerm _ _ -> do
    tseq <- trmToTerm t
    return $ Term_seq tseq
  FOLSign.SPQuantTerm {} ->
      fail "quantification not allowed in argument list"

trmToFunctTrm :: FOLSign.SPTerm -> Result TERM
trmToFunctTrm t = case t of
  FOLSign.SPComplexTerm sym args ->
      if null args
      then return $ symToTerm sym
      else do
        tseq <- mapM trmToTermSeq args
        return $ Funct_term (symToTerm sym) tseq nullRange
  FOLSign.SPQuantTerm {} ->
      fail "quantification not allowed in quantifier-argument list"

-- | converts a custom symbol to a NAME, used in
symToName :: FOLSign.SPSymbol -> NAME
symToName s = case s of
  FOLSign.SPCustomSymbol i -> i
  FOLSign.SPID -> idName
  FOLSign.SPDiv -> divName
  FOLSign.SPComp -> compName
  FOLSign.SPSum -> sumName
  FOLSign.SPConv -> convName
  x -> error $ "symbol not convertible to a name: " ++ show x

symToTerm :: FOLSign.SPSymbol -> TERM
symToTerm s = Name_term $ symToName s

isNullary :: FOLSign.SPTerm -> Bool
isNullary t = case t of
  FOLSign.SPComplexTerm _ [] -> True
  _ -> False

-- representation for true in CL
clTrue :: SENTENCE -- forall x. x=x
clTrue = Quant_sent Universal [Name xName]
         (Atom_sent (Equation (Name_term xName) (Name_term xName)) nullRange
         ) nullRange

-- representation for false in CL
clFalse :: SENTENCE
clFalse = Bool_sent (Negation clTrue) nullRange

-- creates an individual-name out of a NAME by appending "_i" to it
indv :: NAME -> Int -> NAME
indv n i = mkSimpleId (tokStr n ++ "_item_" ++ show i)

-- simple names
xName :: NAME
xName = mkSimpleId "x"

idName :: NAME
idName = mkSimpleId "ID"

divName :: NAME
divName = mkSimpleId "DIV"

compName :: NAME
compName = mkSimpleId "COMP"

sumName :: NAME
sumName = mkSimpleId "SUM"

convName :: NAME
convName = mkSimpleId "CONV"

-- Text-Names
sortRelTrS :: String
sortRelTrS = "SoftFOL_SubsortRelations"

funcMapTrS :: String
funcMapTrS = "SoftFOL_FunctionMaps"

predMapTrS :: String
predMapTrS = "SoftFOL_PredicateMaps"
