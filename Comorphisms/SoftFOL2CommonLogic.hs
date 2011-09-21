{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
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

import Common.ProofTree
import Common.Id
import Common.Result
import qualified Common.AS_Annotation as AS_Anno
import qualified Common.DefaultMorphism as DefaultMorphism
import qualified Common.Lib.Rel as Rel

import Logic.Logic
import Logic.Comorphism

import qualified Data.Set as Set
import qualified Data.Map as Map

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
    ()                       -- Basic spec domain
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
    TEXT                     -- sentence domain
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
  in  return $ ClMor.Morphism src tgt pmp

mapSentence :: FOLSign.Sign -> FOLSign.Sentence -> Result TEXT
mapSentence s f = return $ translate s f

mapSign :: FOLSign.Sign -> ClSign.Sign
mapSign sig =
  let items = Set.map (\t -> mkId [t]) $ Set.fromList $ concat
                                [ Map.keys $ FOLSign.sortMap sig
                                , Map.keys $ FOLSign.funcMap sig
                                , Map.keys $ FOLSign.predMap sig
                                ]
  in  ClSign.Sign items items

-- | translates SoftFOL-theories to CL-theories keeping their names
mapTheory :: (FOLSign.Sign, [AS_Anno.Named FOLSign.Sentence])
             -> Result (ClSign.Sign, [AS_Anno.Named TEXT])
mapTheory (srcSign, srcFormulas) =
  return (mapSign srcSign,
        AS_Anno.makeNamed "SoftFOL_Sign_Trans" (transSign srcSign)
        : map ((uncurry AS_Anno.makeNamed) . transSnd . senAndName) srcFormulas)
  where senAndName :: AS_Anno.Named FOLSign.Sentence -> (String, FOLSign.Sentence)
        senAndName f = (AS_Anno.senAttr f, AS_Anno.sentence f)
        transSnd :: (String, FOLSign.Sentence) -> (String, TEXT)
        transSnd (s, f) = (s, translate srcSign f)

transSign :: FOLSign.Sign -> TEXT
transSign s = Text ( sortRelPhrs (Rel.toMap $ FOLSign.sortRel s)
                  ++ funcMapPhrs (FOLSign.funcMap s)
                  ++ predMapPhrs (FOLSign.predMap s)
                  ) nullRange

-- translates a SoftFOL-theory to a CL-Text
translate :: FOLSign.Sign -> FOLSign.Sentence -> TEXT
translate s f = Text [Sentence $ toSen s f] nullRange

-- creates one-sentence-phrases: forall x. (subSort x) => (superSort x)
sortRelPhrs :: Map.Map FOLSign.SPIdentifier (Set.Set FOLSign.SPIdentifier)
                -> [PHRASE]
sortRelPhrs m =
  Map.foldrWithKey (\subSrt set phrs -> (
    Set.fold (\superSrt phrs2 ->
        Sentence (Quant_sent (Universal [Name xName] (Bool_sent (Implication
            (predicateNames subSrt [xName]) (predicateNames superSrt [xName])
          ) nullRange)) nullRange)
      : phrs2) [] set
    ) ++ phrs) [] m

typesWithIndv :: [Token] -> [(Token, NAME)] -- (type, individual)
typesWithIndv args =
  foldr (\(a, i) resArg -> (a, indv a i) : resArg) [] $ zip args [0..]

-- creates one-sentence-phrases:
-- forall x y z. (if (and (T1 x) (T2 y) (T3 z)) (T4 f[x,y,z]))
funcMapPhrs :: Map.Map Token (Set.Set ([Token], Token)) -> [PHRASE]
funcMapPhrs m =
  Map.foldrWithKey (\f set phrs -> (
    Set.fold (\(args, res) phrs2 ->
      let argsAndNames = typesWithIndv args
      in  Sentence (
            if null args
            then predicateNames res [f]
            else 
              Quant_sent (Universal (map (Name . snd) argsAndNames) (
                Bool_sent (Implication
                    (Bool_sent (Conjunction $
                        map (\(p, x) -> predicateNames p [x]) argsAndNames
                      ) nullRange)
                    (Atom_sent (Atom
                        (Name_term res)
                        [Term_seq $ Funct_term (Name_term f) (
                            map (Term_seq . Name_term . snd) argsAndNames
                          ) nullRange]
                      ) nullRange)
                  ) nullRange
                )) nullRange)
      : phrs2) [] set
    ) ++ phrs) [] m

-- creates one-sentence-phrases:
-- forall x y z. (P[x,y,z]) => (and (T1 x) (T2 y) (T3 z))
predMapPhrs :: Map.Map Token (Set.Set [Token]) -> [PHRASE]
predMapPhrs m =
  Map.foldrWithKey (\prd set phrs -> (
    Set.fold (\args phrs2 ->
      let argsAndNames = typesWithIndv args
      in  Sentence (Quant_sent (Universal (map (Name . snd) argsAndNames) (
              Bool_sent (Implication
                  (predicateNames prd (map snd argsAndNames))
                  (Bool_sent (Conjunction $
                      map (\(p, x) -> predicateNames p [x]) argsAndNames
                    ) nullRange)
                ) nullRange
              )) nullRange)
      : phrs2) [] set
    ) ++ phrs) [] m

toSen :: FOLSign.Sign -> FOLSign.SPTerm -> SENTENCE
toSen s t = case t of
  FOLSign.SPQuantTerm qsym vl f -> quantTrm s qsym vl f
  FOLSign.SPComplexTerm sym args -> case sym of
    FOLSign.SPEqual -> case args of
        [x,y] -> toEquation (x,y)
        l@(_:_:_) -> Bool_sent (
                        Conjunction $ map toEquation $ zip l $ tail l
                    ) nullRange
        x -> error $ "equation needs at least two arguments, but found: " ++ show x
    FOLSign.SPTrue -> clTrue
    FOLSign.SPFalse -> clFalse
    FOLSign.SPOr -> Bool_sent (Disjunction $ map (toSen s) args) nullRange
    FOLSign.SPAnd -> Bool_sent (Conjunction $ map (toSen s) args) nullRange
    FOLSign.SPNot -> case args of
        [x] -> Bool_sent (Negation $ toSen s x) nullRange
        _ -> error $
              "negation can only be applied to a single argument, but found: "
              ++ show t
    FOLSign.SPImplies -> case args of
        [x,y] -> Bool_sent (Implication (toSen s x) (toSen s y)) nullRange
        _ -> error $
              "implication can only be applied to two arguments, but found: "
              ++ show t
    FOLSign.SPImplied -> case args of
        [x,y] -> Bool_sent (Implication (toSen s y) (toSen s x)) nullRange
        _ -> error $
              "implication can only be applied to two arguments, but found: "
              ++ show t
    FOLSign.SPEquiv ->  case args of
        [x,y] -> Bool_sent (Biconditional (toSen s x) (toSen s y)) nullRange
        _ -> error $
              "equivalence can only be applied to two arguments, but found: "
              ++ show t
    _ -> predicateSPTerms (symToTerm sym) args

-- | converts SPEquation to a CL-Equation
toEquation :: (FOLSign.SPTerm, FOLSign.SPTerm) -> SENTENCE
toEquation (x,y) =
  Atom_sent (Equation (trmToTerm x) (trmToTerm y)) nullRange

predicateSPTerms :: TERM -> [FOLSign.SPTerm] -> SENTENCE
predicateSPTerms t args = Atom_sent (Atom t (map trmToTermSeq args)) nullRange

predicateNames :: NAME -> [NAME] -> SENTENCE
predicateNames p xs =
  Atom_sent (Atom (Name_term p) (map (Term_seq . Name_term) xs)) nullRange

predicateTerm :: NAME -> TERM -> SENTENCE
predicateTerm p xs = Atom_sent (Atom (Name_term p) [Term_seq xs]) nullRange

-- Converts a quantified FOL-term to a CL-Quant_sent. Quantifier arguments
-- contain only the inner-most arguments  of the SoftFOL Quantifier in order to
-- convert sentences like
-- @forall s(Y1), t(u(Y2)) .  Y1 /= Y2@
-- to
-- @forall Y1, Y2 . S(Y1) & T(u(Y2)) & U(Y2) => Y1 /= Y2@
-- where S, T and U are the types that Y1, u(Y2) and Y2 must have
-- in order to apply functions/predicates s, t and u to them (defined in
-- funcMap and predMap).
quantTrm :: FOLSign.Sign -> FOLSign.SPQuantSym
            -> [FOLSign.SPTerm] -> FOLSign.SPTerm -> SENTENCE
quantTrm sig qsymm vs f =
  let functions_quant = filter (not . isNullary) vs
      trans_vs = concatMap trmToNameSeq vs
      trans_f = if null functions_quant
                then toSen sig f
                else Bool_sent (Implication
                         (typeSentence sig functions_quant)
                         (toSen sig f)
                       ) nullRange
      quantifier = case qsymm of
        FOLSign.SPForall -> Universal
        FOLSign.SPExists -> Existential
        _ -> error "custom quantifiers not allowed"
  in Quant_sent (quantifier trans_vs trans_f) nullRange

typeSentence :: FOLSign.Sign -> [FOLSign.SPTerm] -> SENTENCE
typeSentence sig vs = case vs of
  [] -> clTrue
  [v] -> typeSentence1 sig v      -- v = f(x,y,z)
  _ -> Bool_sent (Conjunction $ map (typeSentence1 sig) vs) nullRange

typeSentence1 :: FOLSign.Sign -> FOLSign.SPTerm -> SENTENCE
typeSentence1 sig v = case v of
  FOLSign.SPComplexTerm _ [] ->
    error "bug (typeSentence1): nullary functions should not occur here"
  FOLSign.SPComplexTerm sym args -> typeSentenceGetTypes sig (symToName sym) args
  FOLSign.SPQuantTerm _ _ _ ->
    error "quantification not allowed in quantifier-argument list"

typeSentenceGetTypes :: FOLSign.Sign -> FOLSign.SPIdentifier -> [FOLSign.SPTerm]
                        -> SENTENCE
typeSentenceGetTypes sig symN args =
  case (Map.lookup symN $ FOLSign.funcMap sig) of
    Nothing -> case (Map.lookup symN $ FOLSign.predMap sig) of
      Nothing -> case (Map.lookup symN $ FOLSign.sortMap sig) of
        Nothing -> error $ "symbol has no type: " ++ show symN
        Just _ -> typeSentencesSort args symN
      Just ts -> typeSentencesDisjPred sig args $ Set.elems ts
    Just ts -> typeSentencesDisjFunc sig args $ Set.elems ts

typeSentencesDisjPred :: FOLSign.Sign -> [FOLSign.SPTerm]
                         -> [[FOLSign.SPIdentifier]]
                         -> SENTENCE
typeSentencesDisjPred sig args typeSet = case typeSet of
  [t] -> tsdp1 t
  _ -> Bool_sent (Disjunction $ map tsdp1 typeSet) nullRange
  where tsdp1 :: [FOLSign.SPIdentifier] -> SENTENCE
        tsdp1 t = Bool_sent (Conjunction $
          map (\(arg, argType) -> case arg of
              FOLSign.SPComplexTerm _ [] ->
                predicateNames argType [trmToName arg]
              FOLSign.SPComplexTerm _ _ ->
                typeSentence1 sig arg
              FOLSign.SPQuantTerm _ _ _ ->
                error "quantification not allowed in quantifier-argument list"
            ) $ zip args t
          ) nullRange

typeSentencesDisjFunc :: FOLSign.Sign -> [FOLSign.SPTerm]
                         -> [([FOLSign.SPIdentifier], FOLSign.SPIdentifier)]
                         -> SENTENCE
typeSentencesDisjFunc sig args typeSet = case typeSet of
  [t] -> tsdf1 t
  _ -> Bool_sent (Disjunction $ map tsdf1 typeSet) nullRange
  where tsdf1 :: ([FOLSign.SPIdentifier], FOLSign.SPIdentifier) -> SENTENCE
        tsdf1 (t, resType) = Bool_sent (Conjunction $
            concatMap (\(arg, argType) -> case arg of
              FOLSign.SPComplexTerm _ [] ->
                [predicateNames argType [trmToName arg]]
              FOLSign.SPComplexTerm _ _ ->
                [ predicateTerm resType (trmToFunctTrm arg)
                , typeSentence1 sig arg]
              FOLSign.SPQuantTerm _ _ _ ->
                error "quantification not allowed in quantifier-argument list"
            ) $ zip args t
          ) nullRange

typeSentencesSort :: [FOLSign.SPTerm] -> FOLSign.SPIdentifier
                     -> SENTENCE
typeSentencesSort args srt = case args of
  [] -> error $ "no arguments for sort " ++ show srt
  [arg] -> predicateTerm srt (trmToFunctTrm arg)
  _ -> Bool_sent (Conjunction $
          map (\arg -> predicateTerm srt (trmToFunctTrm arg)) args
        ) nullRange

trmToName :: FOLSign.SPTerm -> NAME
trmToName t  = case t of
  FOLSign.SPComplexTerm sym _ -> symToName sym
  x -> error $ "quantification not convertible to a name: " ++ show x

-- converts an @SPTerm@ to @[NAME_OR_SEQMARK]@ as an argument for a quantifier
-- using only the inner-most arguments
trmToNameSeq :: FOLSign.SPTerm -> [NAME_OR_SEQMARK]
trmToNameSeq t = case t of
  FOLSign.SPComplexTerm sym [] -> [Name $ symToName sym]
  FOLSign.SPComplexTerm _ args -> concatMap trmToNameSeq args
  FOLSign.SPQuantTerm _ _ _ ->
      error "quantification not allowed in quantifier-argument list"

-- converts an SPTerm to a TERM, i.e. for the arguments of an equation
trmToTerm :: FOLSign.SPTerm -> TERM
trmToTerm t = case t of
  FOLSign.SPQuantTerm _ _ _ -> error "quantification not allowed for a term"
  FOLSign.SPComplexTerm _ [] -> Name_term $ trmToName t
  FOLSign.SPComplexTerm _ _ -> trmToFunctTrm t

-- Converts an SPTerm to TERM_SEQ as an argument for a quantifier
trmToTermSeq :: FOLSign.SPTerm -> TERM_SEQ
trmToTermSeq t = Term_seq $ case t of
  FOLSign.SPComplexTerm _ _ -> trmToTerm t
  FOLSign.SPQuantTerm _ _ _ ->
      error "quantification not allowed in argument list"

trmToFunctTrm :: FOLSign.SPTerm -> TERM
trmToFunctTrm arg = case arg of
  FOLSign.SPComplexTerm sym args ->
      Funct_term (symToTerm sym) (map trmToTermSeq args) nullRange
  FOLSign.SPQuantTerm _ _ _ -> 
      error "quantification not allowed in quantifier-argument list"

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
clTrue :: SENTENCE --forall x. x=x
clTrue = Quant_sent (Universal [Name xName]
            $ Atom_sent (Equation (Name_term xName) (Name_term xName)) nullRange
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
