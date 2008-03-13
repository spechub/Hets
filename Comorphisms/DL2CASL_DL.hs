{- |
Module      :  $Header$
Description :  Comorphism from DL to CASL_DL
Copyright   :  (c) Dominik Luecke and Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

The translating comorphism from DL to CASL_DL basically this is an
identity comorphism from SROIQ(D) to SROIQ(D)
-}

module Comorphisms.DL2CASL_DL 
    (
     DL2CASL_DL(..)
    )
    where

import Logic.Logic
import Logic.Comorphism
import Common.AS_Annotation
import Common.Result
import Common.Id

-- DL
import DL.Logic_DL as LDL
import DL.AS as ADL
import qualified DL.Sign as SDL

--CASL_DL = codomain
import CASL_DL.Logic_CASL_DL
import CASL_DL.AS_CASL_DL
import CASL_DL.StatAna -- DLSign
import CASL.AS_Basic_CASL
import CASL.Sign
import CASL_DL.Sign
import CASL.Morphism
import qualified CASL_DL.PredefinedSign as PS

data DL2CASL_DL = DL2CASL_DL deriving (Show)

instance Language DL2CASL_DL

thing :: SORT
thing = PS.topSort

dataD :: SORT
dataD = PS.topSortD

instance Comorphism
    DL2CASL_DL      -- comorphism
    DL              -- lid domain
    ()              -- sublogics domain
    DLBasic         -- Basic spec domain
    DLBasicItem     -- sentence domain
    ()              -- symbol items domain
    ()              -- symbol map items domain
    SDL.Sign        -- signature domain
    SDL.DLMorphism  -- morphism domain
    SDL.DLSymbol    -- symbol domain
    SDL.RawDLSymbol -- rawsymbol domain
    ()              -- proof tree codomain
    CASL_DL         -- lid codomain
    ()              -- sublogics codomain
    DL_BASIC_SPEC   -- Basic spec codomain
    DLFORMULA       -- sentence codomain
    SYMB_ITEMS      -- symbol items codomain
    SYMB_MAP_ITEMS  -- symbol map items codomain
    DLSign          -- signature codomain
    DLMor           -- morphism codomain
    Symbol          -- symbol codomain
    RawSymbol       -- rawsymbol codomain
    ()              -- proof tree domain
        where
          sourceLogic DL2CASL_DL    = DL
          sourceSublogic DL2CASL_DL = ()      
          targetLogic DL2CASL_DL    = CASL_DL
          mapSublogic DL2CASL_DL _  = Just ()
          map_theory DL2CASL_DL     = map_DL_theory
          map_morphism DL2CASL_DL   = error "map_morphism OWL2CASL_DL"

map_DL_theory :: (SDL.Sign, [Named DLBasicItem]) ->
                 Result (DLSign, [Named DLFORMULA])
map_DL_theory (sig, n_sens) = 
    do
      let osig = emptySign emptyCASL_DLSign
      oforms <- mapM (map_named_basic_item sig) n_sens
      return (osig, concat $ oforms)

map_named_basic_item :: SDL.Sign -> Named DLBasicItem -> Result [Named DLFORMULA]
map_named_basic_item sign sens = 
    let
        s = sentence sens
    in
      do 
        os <- map_basic_item sign s
        return $ map (\x -> sens {sentence = x}) os

map_basic_item :: SDL.Sign -> DLBasicItem ->  Result [DLFORMULA]
map_basic_item sig sent = 
    case sent of
      DLClass iid props _ rn -> 
          do
            propsM <- mapM (map_class_property sig iid) props
            return $ concat $ propsM
      DLObjectProperty iid dc rc prel chars para rn -> error ""
      DLDataProperty iid dc rc prel chars para rn -> error ""
      DLIndividual iid tp fts irel para rn -> error ""
      DLMultiIndi _ _ _ _ _ rn -> fatal_error "Error during analysis, \
                                            \ Multi-Individual was not \
                                            \ expanded, bailing out." rn

map_class_property :: SDL.Sign -> Id -> DLClassProperty -> Result [DLFORMULA]
map_class_property sig iid dcp = 
    let
        a = mkSimpleId "a"
    in
    case dcp of
      DLSubClassof con rn   -> 
          mapM (\x -> 
                do
                  ct <- (map_concept sig a x)
                  return $ Quantification Universal [Var_decl [a] thing nullRange]
                             (Implication
                              (Predication
                               (Qual_pred_name iid (Pred_type [thing] nullRange) nullRange)
                               [Qual_var a thing nullRange]
                               nullRange)
                              ct
                              True
                              nullRange) rn) con
      DLEquivalentTo con rn ->
          mapM (\x -> 
                do
                  ct <- (map_concept sig a x)
                  return $ Quantification Universal [Var_decl [a] thing nullRange]
                             (Equivalence
                              (Predication
                               (Qual_pred_name iid (Pred_type [thing] nullRange) nullRange)
                               [Qual_var a thing nullRange]
                               nullRange)
                              ct
                              nullRange) rn) con
      DLDisjointWith con rn -> 
          do
            mapM (\x ->
                  do
                    ct <- (map_concept sig a x)
                    return $ Quantification Universal [Var_decl [a] thing nullRange]
                               (Negation
                                (Conjunction
                                 [Predication
                                  (Qual_pred_name iid (Pred_type [thing] nullRange) nullRange)
                                  [Qual_var a thing nullRange]
                                  nullRange,
                                  ct]
                                 nullRange)
                                nullRange)
                               rn) con

map_concept :: SDL.Sign -> Token -> DLConcept -> Result DLFORMULA
map_concept sign iid con = 
    let
        b = mkSimpleId "b"
    in
    case con of 
      DLAnd c1 c2 rn -> 
          do
            c1t <- map_concept sign iid c1
            c2t <- map_concept sign iid c2
            return $   Conjunction [c1t,c2t] rn
      DLOr c1 c2 rn -> 
          do
            c1t <- map_concept sign iid c1
            c2t <- map_concept sign iid c2
            return $   Disjunction [c1t,c2t] rn
      DLXor c1 c2 rn ->
          do
            c1t <- map_concept sign iid c1
            c2t <- map_concept sign iid c2
            return $ Conjunction
                 [Disjunction [c1t,c2t] nullRange,
                  Negation (Conjunction [c1t,c2t] nullRange)
                    nullRange]
                 rn
      DLNot c1 rn -> 
          do
            c1t <- map_concept sign iid c1
            return $ Negation c1t rn
      DLClassId c1 rn -> 
          do
            return $ Predication
                       (Qual_pred_name c1 (Pred_type [thing] nullRange) nullRange)
                       [Qual_var iid thing nullRange]
                       nullRange
      DLOneOf iids rn  -> fatal_error "oneOf nyi" rn
      DLSome rid conc rn -> 
          do
            ct <- map_concept sign iid conc
            return $ Quantification Existential [Var_decl [b] thing nullRange]
                    (Conjunction
                       [Predication
                          (Qual_pred_name rid (Pred_type [thing, thing] nullRange) nullRange)
                          [Qual_var iid thing nullRange, Qual_var b thing nullRange]
                          nullRange,
                       ct]
                       nullRange)
                    rn
      DLHas rid indi rn -> 
             return $ Predication
                (Qual_pred_name rid (Pred_type [thing, thing] nullRange) nullRange)
                [Qual_var iid thing nullRange, Qual_var (restoreToken indi) thing nullRange]
                rn
      DLValue rid indi rn -> 
             return $ Predication
                (Qual_pred_name rid (Pred_type [thing, thing] nullRange) nullRange)
                [Qual_var iid thing nullRange, Qual_var (restoreToken indi) thing nullRange]
                rn
      DLOnlysome rel cons rn ->  map_concept sign iid $ expand (DLOnlysome rel cons rn)
      DLOnly _ _ _ -> fatal_error "nyi" nullRange
      DLMin _ _ _ _ -> fatal_error "nyi" nullRange
      DLMax _ _ _ _ -> fatal_error "nyi" nullRange
      DLExactly _ _ _ _ -> fatal_error "nyi" nullRange                       
      DLSelf _ -> fatal_error "nyi" nullRange                       

restoreToken :: Id -> Token
restoreToken = head . getTokens
