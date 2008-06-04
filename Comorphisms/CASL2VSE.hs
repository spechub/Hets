{- |
Module      :  $Header$
Description :  embedding from CASL to VSE
Copyright   :  (c) C. Maeder, DFKI Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The embedding comorphism from CASL to VSE.
-}

module Comorphisms.CASL2VSE (CASL2VSE(..)) where

import qualified Data.Set as Set

import Logic.Logic
import Logic.Comorphism

import CASL.Logic_CASL
import CASL.Sublogic as SL
import CASL.Sign
import CASL.AS_Basic_CASL
import CASL.Morphism

import VSE.Logic_VSE
import VSE.As

-- | The identity of the comorphism
data CASL2VSE = CASL2VSE deriving (Show)

instance Language CASL2VSE -- default definition is okay

instance Comorphism CASL2VSE
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               Symbol RawSymbol Q_ProofTree
               VSE ()
               VSEBasicSpec Sentence SYMB_ITEMS SYMB_MAP_ITEMS
               VSESign
               VSEMor
               Symbol RawSymbol () where
    sourceLogic CASL2VSE = CASL
    sourceSublogic CASL2VSE = SL.top
    targetLogic CASL2VSE = VSE
    mapSublogic CASL2VSE _ = Just ()
    map_theory CASL2VSE = return . simpleTheoryMapping mapSig mapSen
    map_morphism CASL2VSE = return . mapMor
    map_sentence CASL2VSE _ = return . mapSen
    map_symbol CASL2VSE = Set.singleton . mapSym
    has_model_expansion CASL2VSE = True
    is_weakly_amalgamable CASL2VSE = True
    isInclusionComorphism CASL2VSE = True

mapSig :: CASLSign -> VSESign
mapSig sign = sign { extendedInfo = emptyProcs, sentences = [] }

mapMor :: CASLMor -> VSEMor
mapMor m = m
  { msource = mapSig $ msource m
  , mtarget = mapSig $ mtarget m }

mapSym :: Symbol -> Symbol
mapSym = id  -- needs to be changed once proc symbols are added

mapSen :: CASLFORMULA -> Sentence
mapSen f = case f of
    Quantification q vs frm ps ->
        Quantification q vs (mapSen frm) ps
    Conjunction fs ps ->
        Conjunction (map mapSen fs) ps
    Disjunction fs ps ->
        Disjunction (map mapSen fs) ps
    Implication f1 f2 b ps ->
        Implication (mapSen f1) (mapSen f2) b ps
    Equivalence f1 f2 ps ->
        Equivalence (mapSen f1) (mapSen f2) ps
    Negation frm ps -> Negation (mapSen frm) ps
    True_atom ps -> True_atom ps
    False_atom ps -> False_atom ps
    Existl_equation t1 t2 ps ->
        Existl_equation (mapTERM t1) (mapTERM t2) ps
    Strong_equation t1 t2 ps ->
        Strong_equation (mapTERM t1) (mapTERM t2) ps
    Predication pn as qs ->
        Predication pn (map mapTERM as) qs
    Definedness t ps -> Definedness (mapTERM t) ps
    Membership t ty ps -> Membership (mapTERM t) ty ps
    Sort_gen_ax constrs isFree -> Sort_gen_ax constrs isFree
    _ -> error "CASL2VSE.mapSen"

mapTERM :: TERM () -> TERM Dlformula
mapTERM t = case t of
    Qual_var v ty ps -> Qual_var v ty ps
    Application opsym as qs  -> Application opsym (map mapTERM as) qs
    Sorted_term trm ty ps -> Sorted_term (mapTERM trm) ty ps
    Cast trm ty ps -> Cast (mapTERM trm) ty ps
    Conditional t1 f t2 ps ->
       Conditional (mapTERM t1) (mapSen f) (mapTERM t2) ps
    _ -> error "CASL2VSE.mapTERM"
