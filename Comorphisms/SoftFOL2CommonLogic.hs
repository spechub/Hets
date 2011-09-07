{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  Coding of SoftFOL into CommonLogic
Copyright   :  (c) Eugen Kuksa and Uni Bremen 2007
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

import Logic.Logic
import Logic.Comorphism

import qualified Data.Set as Set

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
    NAME                     -- symbol items domain
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
mapMor mor = undefined {-
  let src = mapSign $ PMor.source mor
      tgt = mapSign $ PMor.target mor
      pmp = PMor.propMap mor
  in  return $ ClMor.Morphism src tgt pmp
-}

mapSentence :: FOLSign.Sign -> FOLSign.Sentence -> Result TEXT
mapSentence _ f = return $ translate f

mapSign :: FOLSign.Sign -> ClSign.Sign
mapSign sig = undefined
--  ClSign.unite (ClSign.Sign (PSign.items sig) (PSign.items sig)) $ baseSig

-- | translates FOL-theories to CL-theories keeping their names
mapTheory :: (FOLSign.Sign, [AS_Anno.Named FOLSign.Sentence])
             -> Result (ClSign.Sign, [AS_Anno.Named TEXT])
mapTheory (srcSign, srcFormulas) = 
  return (mapSign srcSign,
        map ((uncurry AS_Anno.makeNamed) . elimModSnd . senAndName) srcFormulas)
  where senAndName :: AS_Anno.Named FOLSign.Sentence -> (String, FOLSign.Sentence)
        senAndName f = (AS_Anno.senAttr f, AS_Anno.sentence f)
        elimModSnd :: (String, FOLSign.Sentence) -> (String, TEXT)
        elimModSnd (s, f) = (s, translate f)

translate :: FOLSign.Sentence -> TEXT
translate f = Text [Sentence $ toSen f] nullRange

toSen :: FOLSign.SPTerm -> SENTENCE
toSen t = case t of
  FOLSign.SPQuantTerm qsym vl f -> quantTrm qsym vl f
  FOLSign.SPComplexTerm sym args -> case sym of
    FOLSign.SPEqual -> case args of
        [x,y] -> toEquation (x,y)
        l@(_:_:_) -> Bool_sent (
                        Conjunction $ map toEquation $ zip l $ tail l
                    ) nullRange
        x -> error $ "equation needs at least two arguments, but found: " ++ show x
    FOLSign.SPTrue -> clTrue
    FOLSign.SPFalse -> clFalse
    FOLSign.SPOr -> Bool_sent (Disjunction $ map toSen args) nullRange
    FOLSign.SPAnd -> Bool_sent (Conjunction $ map toSen args) nullRange
    FOLSign.SPNot -> case args of
        [x] -> Bool_sent (Negation $ toSen x) nullRange
        x -> error $
              "negation can only be applied to a single argument, but found: "
              ++ show x
    FOLSign.SPImplies -> case args of
        [x,y] -> Bool_sent (Implication (toSen x) (toSen y)) nullRange
        x -> error $
              "implication can only be applied to two arguments, but found: "
              ++ show x
    FOLSign.SPImplied -> case args of -- --------------****** what is SPImplied?
        [x,y] -> Bool_sent (Implication (toSen y) (toSen x)) nullRange
        x -> error $
              "implication can only be applied to two arguments, but found: "
              ++ show x
    FOLSign.SPEquiv ->  case args of
        [x,y] -> Bool_sent (Biconditional (toSen x) (toSen y)) nullRange
        x -> error $
              "equivalence can only be applied to two arguments, but found: "
              ++ show x
    FOLSign.SPID -> predicate (Name_term idName) args
    FOLSign.SPDiv -> predicate (Name_term divName) args
    FOLSign.SPComp -> predicate (Name_term compName) args
    FOLSign.SPSum -> predicate (Name_term sumName) args
    FOLSign.SPConv -> predicate (Name_term convName) args
    FOLSign.SPCustomSymbol _ -> predicate (symToTerm sym) args

-- | converts a quantified FOL-term to a CL-Quant_sent
quantTrm :: FOLSign.SPQuantSym -> [FOLSign.SPTerm] -> FOLSign.SPTerm -> SENTENCE
quantTrm qsymm vl f =
  let trans_vl = map sptermToNameSeq vl
      trans_f = toSen f
      quantifier = case qsymm of
        FOLSign.SPForall -> Universal
        FOLSign.SPExists -> Existential
        _ -> error "custom quantifiers not allowed"
  in Quant_sent (quantifier trans_vl trans_f) nullRange

-- | converts SPEquation to an CL-Equation
toEquation :: (FOLSign.SPTerm, FOLSign.SPTerm) -> SENTENCE
toEquation (x,y) =
  Atom_sent (Equation (sptermToTerm x) (sptermToTerm y)) nullRange

symToTerm :: FOLSign.SPSymbol -> TERM
symToTerm s = case s of
  FOLSign.SPCustomSymbol i -> Name_term i
  x -> error $ "symbol not allowed for a term: " ++ show x

predicate :: TERM -> [FOLSign.SPTerm] -> SENTENCE
predicate t args =
  Atom_sent (Atom t (map sptermToTermSeq args)) nullRange

-- converts an SPTerm to a TERM, i.e. for the arguments of an equation
sptermToTerm :: FOLSign.SPTerm -> TERM
sptermToTerm t = case t of
  FOLSign.SPQuantTerm qsym vl f -> error "quantification not allowed for a term"
  FOLSign.SPComplexTerm sym args -> case sym of
      FOLSign.SPCustomSymbol i -> Name_term i
      x -> error $ "symbol not allowed as a term: " ++ show x

-- | converts an SPTerm to TERM_SEQ as an argument for a quantifier
sptermToTermSeq :: FOLSign.SPTerm -> TERM_SEQ
sptermToTermSeq t = case t of
  FOLSign.SPComplexTerm sym [] -> Term_seq $ symToTerm sym
  FOLSign.SPComplexTerm _ _ -> error "predicates not allowed in argument list"
  FOLSign.SPQuantTerm _ _ _ ->
      error "quantification not allowed in argument list"

-- | converts an SPTerm to NAME_OR_SEQMARK as an argument for a predicate
sptermToNameSeq :: FOLSign.SPTerm -> NAME_OR_SEQMARK
sptermToNameSeq t = case t of
  FOLSign.SPComplexTerm sym [] -> Name $ symToName sym
  FOLSign.SPComplexTerm _ _ ->
      error "predicates not allowed in argument list"
  FOLSign.SPQuantTerm _ _ _ ->
      error "quantification not allowed in argument list"

-- | converts a custom symbol to a NAME, used in
symToName :: FOLSign.SPSymbol -> NAME
symToName s = case s of
  FOLSign.SPCustomSymbol i -> i
  x -> error $ "symbol not convertible to a name: " ++ show x

-- representation for true in CL
clTrue :: SENTENCE --forall x. x=x
clTrue = Quant_sent (Universal [Name xName]
            $ Atom_sent (Equation (Name_term xName) (Name_term xName)) nullRange
          ) nullRange

-- representation for false in CL
clFalse :: SENTENCE
clFalse = Bool_sent (Negation clTrue) nullRange

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
