{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  Inclusion of CASL_DL into CASL
Copyright   :  (c) Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (via Logic.Logic)

-}

module Comorphisms.CASL_DL2CASL
    (
     CASL_DL2CASL(..)
    )
    where

import Logic.Logic
import Logic.Comorphism

import Common.AS_Annotation
import Common.ProofTree
import Common.Result
import qualified Common.Lib.Rel as Rel

--CASL_DL = domain
import CASL_DL.PredefinedCASLAxioms
import CASL_DL.Logic_CASL_DL
import CASL_DL.AS_CASL_DL
import CASL_DL.Sign()
import CASL_DL.PredefinedSign
import CASL_DL.StatAna -- DLSign
import CASL_DL.Sublogics

--CASL = codomain
import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism
import CASL.Sublogic as Sublogic

import qualified Data.Set as Set

data CASL_DL2CASL = CASL_DL2CASL deriving Show

instance Language CASL_DL2CASL

instance Comorphism
    CASL_DL2CASL    -- comorphism
    CASL_DL         -- lid domain
    CASL_DL_SL      -- sublogics domain
    DL_BASIC_SPEC   -- Basic spec domain
    DLFORMULA       -- sentence domain
    SYMB_ITEMS      -- symbol items domain
    SYMB_MAP_ITEMS  -- symbol map items domain
    DLSign          -- signature domain
    DLMor           -- morphism domain
    Symbol          -- symbol domain
    RawSymbol       -- rawsymbol domain
    ProofTree     -- proof tree codomain
    CASL            -- lid codomain
    CASL_Sublogics  -- sublogics codomain
    CASLBasicSpec   -- Basic spec codomain
    CASLFORMULA     -- sentence codomain
    SYMB_ITEMS      -- symbol items codomain
    SYMB_MAP_ITEMS  -- symbol map items codomain
    CASLSign        -- signature codomain
    CASLMor         -- morphism codomain
    Symbol          -- symbol codomain
    RawSymbol       -- rawsymbol codomain
    ProofTree     -- proof tree domain
    where
      sourceLogic CASL_DL2CASL    = CASL_DL
      targetLogic CASL_DL2CASL    = CASL
      sourceSublogic CASL_DL2CASL = SROIQ
      mapSublogic CASL_DL2CASL _  = Just $ Sublogic.caslTop
                      { sub_features = LocFilSub
                      , cons_features = emptyMapConsFeature }
      map_symbol  CASL_DL2CASL _  = Set.singleton
      map_sentence CASL_DL2CASL   = trSentence
      map_morphism CASL_DL2CASL   = mapMor
      map_theory   CASL_DL2CASL   = trTheory
      isInclusionComorphism CASL_DL2CASL = True
      has_model_expansion CASL_DL2CASL = True

-- ^ mapping of morphims, we just forget the
-- ^ additional features
mapMor :: DLMor -> Result CASLMor
mapMor inMor =
    let
        ms = trSign $ msource inMor
        mt = trSign $ mtarget inMor
        sm = sort_map inMor
        fm = op_map inMor
        pm = pred_map inMor
    in return (embedMorphism () ms mt)
        { sort_map = sm
        , op_map = fm
        , pred_map = pm }

-- ^ we forget additional information in the signature
projectToCASL :: DLSign -> CASLSign
projectToCASL dls = dls
                    {
                      sentences = []
                    , extendedInfo = ()
                    }

-- ^ Thing is established as the TopSort of all sorts
-- ^ defined in the CASL_DL spec, a predefined signature
-- ^ is added
trSign :: DLSign -> CASLSign
trSign inSig =
    let
        inC = projectToCASL inSig `uniteCASLSign` predefSign
        inSorts  = sortSet inSig
        inData   = sortSet dataSig_CASL
    in
      inC
      {
        sortSet = Set.insert topSort $  Set.insert topSortD $ sortSet inC,
        sortRel =
                  Set.fold (\x -> Rel.insert x topSortD)
                  (Set.fold (\x -> Rel.insert x topSort)
                   (sortRel inC) inSorts) $
                  Set.delete topSortD inData
      }

-- ^ translation of the signature
-- ^ predefined axioms are added

-- Translation of theories
trTheory :: (DLSign, [Named (FORMULA DL_FORMULA)]) ->
            Result (CASLSign, [Named (FORMULA ())])
trTheory (inSig, inForms) = do
      outForms <- mapR (trNamedSentence inSig) inForms
      return (trSign inSig, predefinedAxioms ++ outForms)

-- ^ translation of named sentences
trNamedSentence :: DLSign -> Named (FORMULA DL_FORMULA) ->
                   Result (Named (FORMULA ()))
trNamedSentence inSig inForm = do
        outSen <- trSentence inSig $ sentence inForm
        return $ mapNamed (const outSen) inForm

-- ^ translation of sentences
trSentence ::  DLSign -> FORMULA DL_FORMULA -> Result (FORMULA ())
trSentence inSig inF =
      case inF of
        Quantification qf vs frm rn ->
            do
              outF <- trSentence inSig frm
              return (Quantification qf vs outF rn)
        Conjunction fns rn ->
            do
              outF <- mapR (trSentence inSig) fns
              return (Conjunction outF rn)
        Disjunction fns rn ->
            do
              outF <- mapR (trSentence inSig) fns
              return (Disjunction outF rn)
        Implication f1 f2 b rn ->
            do
              out1 <- trSentence inSig f1
              out2 <- trSentence inSig f2
              return (Implication out1 out2 b rn)
        Equivalence f1 f2 rn ->
            do
              out1 <- trSentence inSig f1
              out2 <- trSentence inSig f2
              return (Equivalence out1 out2 rn)
        Negation frm rn ->
            do
              outF <- trSentence inSig frm
              return (Negation outF rn)
        True_atom rn -> return (True_atom rn)
        False_atom rn -> return (False_atom rn)
        Predication pr trm rn ->
            do
              ot <- mapR (trTerm inSig) trm
              return (Predication pr ot rn)
        Definedness tm rn ->
            do
              ot <- trTerm inSig tm
              return (Definedness ot rn)
        Existl_equation t1 t2 rn ->
            do
              ot1 <- trTerm inSig t1
              ot2 <- trTerm inSig t2
              return (Existl_equation ot1 ot2 rn)
        Strong_equation t1 t2 rn ->
            do
              ot1 <- trTerm inSig t1
              ot2 <- trTerm inSig t2
              return (Strong_equation ot1 ot2 rn)
        Membership t1 st rn ->
            do
              ot <- trTerm inSig t1
              return (Membership ot st rn)
        Mixfix_formula trm ->
             do
              ot <- trTerm inSig trm
              return (Mixfix_formula ot)
        Unparsed_formula str rn ->
            return (Unparsed_formula str rn)
        Sort_gen_ax cstr ft ->
            return (Sort_gen_ax cstr ft)
        QuantOp _ _ _ -> fail "CASL_DL2CASL.QuantOp"
        QuantPred _ _ _ -> fail "CASL_DL2CASL.QuantPred"
        ExtFORMULA form ->
            case form of
              Cardinality _ _ _ _ _ _ ->
                    fail "Mapping of cardinality not implemented"

-- ^ translation of terms
trTerm :: DLSign -> TERM DL_FORMULA -> Result (TERM ())
trTerm inSig inF =
    case inF of
      Qual_var v s rn -> return (Qual_var v s rn)
      Application os tms rn ->
          do
            ot <- mapR (trTerm inSig) tms
            return (Application os ot rn)
      Sorted_term trm st rn ->
          do
            ot <- trTerm inSig trm
            return (Sorted_term ot st rn)
      Cast trm st rn ->
          do
            ot <- trTerm inSig trm
            return (Cast ot st rn)
      Conditional t1 frm t2 rn ->
          do
            ot1 <- trTerm inSig t1
            ot2 <- trTerm inSig t2
            of1 <- trSentence inSig frm
            return (Conditional ot1 of1 ot2 rn)
      Unparsed_term str rn -> return (Unparsed_term str rn)
      Mixfix_qual_pred ps  -> return (Mixfix_qual_pred ps)
      Mixfix_term trm ->
          do
            ot <- mapR (trTerm inSig) trm
            return (Mixfix_term ot)
      Mixfix_token tok         -> return (Mixfix_token tok)
      Mixfix_sorted_term st rn -> return (Mixfix_sorted_term st rn)
      Mixfix_cast st rn        -> return (Mixfix_cast st rn)
      Mixfix_parenthesized trm rn ->
          do
            ot <- mapR (trTerm inSig) trm
            return (Mixfix_parenthesized ot rn)
      Mixfix_bracketed trm rn ->
          do
            ot <- mapR (trTerm inSig) trm
            return (Mixfix_bracketed ot rn)
      Mixfix_braced trm rn ->
          do
            ot <-  mapR (trTerm inSig) trm
            return (Mixfix_braced ot rn)
