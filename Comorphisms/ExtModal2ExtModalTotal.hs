{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./Comorphisms/ExtModal2ExtModalTotal.hs
Description :  coding out subsorting
Copyright   :  (c) C. Maeder DFKI GmbH 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

Coding out subsorting (SubPCFOL= -> PCFOL=),
   following Chap. III:3.1 of the CASL Reference Manual
-}

module Comorphisms.ExtModal2ExtModalTotal where

import Logic.Logic
import Logic.Comorphism

import qualified Data.Map as Map
import qualified Data.Set as Set

import qualified Common.Lib.MapSet as MapSet
import Common.AS_Annotation
import Common.ProofUtils

-- CASL
import CASL.AS_Basic_CASL
import CASL.Fold
import CASL.Morphism
import CASL.Sign
import CASL.Simplify
import CASL.Sublogic
import CASL.Utils

import ExtModal.Logic_ExtModal
import ExtModal.AS_ExtModal
import ExtModal.ExtModalSign
import ExtModal.StatAna
import ExtModal.Sublogic as EM

import Comorphisms.CASL2SubCFOL

-- | The identity of the comorphism
data ExtModal2ExtModalTotal = ExtModal2ExtModalTotal deriving Show

instance Language ExtModal2ExtModalTotal -- default definition is okay

instance Comorphism ExtModal2ExtModalTotal
               ExtModal ExtModalSL EM_BASIC_SPEC ExtModalFORMULA SYMB_ITEMS
               SYMB_MAP_ITEMS ExtModalSign ExtModalMorph
               Symbol RawSymbol ()
               ExtModal ExtModalSL EM_BASIC_SPEC ExtModalFORMULA SYMB_ITEMS
               SYMB_MAP_ITEMS ExtModalSign ExtModalMorph
               Symbol RawSymbol () where
    sourceLogic ExtModal2ExtModalTotal = ExtModal
    sourceSublogic ExtModal2ExtModalTotal = mkTop maxSublogic
    targetLogic ExtModal2ExtModalTotal = ExtModal
    mapSublogic ExtModal2ExtModalTotal sl = Just
      $ if has_part sl then sl
        { has_part = False -- partiality is coded out
        , has_pred = True
        , which_logic = max Horn $ which_logic sl
        , has_eq = True} else sl
    map_theory ExtModal2ExtModalTotal (sig, sens) = let
      bsrts = emsortsWithBottom sig
      sens1 = generateAxioms True bsrts sig
      sens2 = map (mapNamed (noCondsEMFormula . simplifyEMFormula
                             . codeEMFormula bsrts)) sens
      in return
             ( emEncodeSig bsrts sig
             , nameAndDisambiguate $ sens1 ++ sens2)
    map_morphism ExtModal2ExtModalTotal mor@Morphism
     {msource = src, mtarget = tar}
        = return
        mor { msource = emEncodeSig (emsortsWithBottom src) src
            , mtarget = emEncodeSig (emsortsWithBottom tar) tar
            , op_map = Map.map (\ (i, _) -> (i, Total)) $ op_map mor }
    map_sentence ExtModal2ExtModalTotal sig sen = let
        bsrts = emsortsWithBottom sig
        in return $ simplifyEMFormula $ codeEMFormula bsrts sen
    map_symbol ExtModal2ExtModalTotal _ s =
      Set.singleton s { symbType = totalizeSymbType $ symbType s }
    has_model_expansion ExtModal2ExtModalTotal = True
    is_weakly_amalgamable ExtModal2ExtModalTotal = True

emEncodeSig :: Set.Set SORT -> Sign f EModalSign -> Sign f EModalSign
emEncodeSig bsrts sig = (encodeSig bsrts sig)
  { extendedInfo = let extInfo = extendedInfo sig in
      extInfo { flexOps = MapSet.map mkTotal $ flexOps extInfo }}

emsortsWithBottom :: Sign f e -> Set.Set SORT
emsortsWithBottom sig = sortsWithBottom NoMembershipOrCast sig Set.empty

simplifyEM :: EM_FORMULA -> EM_FORMULA
simplifyEM = mapExtForm simplifyEMFormula

simplifyEMFormula :: FORMULA EM_FORMULA -> FORMULA EM_FORMULA
simplifyEMFormula = simplifyFormula simplifyEM

noCondsEM :: EM_FORMULA -> EM_FORMULA
noCondsEM = mapExtForm noCondsEMFormula

noCondsEMFormula :: FORMULA EM_FORMULA -> FORMULA EM_FORMULA
noCondsEMFormula = codeOutConditionalF noCondsEM

codeEM :: Set.Set SORT -> EM_FORMULA -> EM_FORMULA
codeEM = mapExtForm . codeEMFormula

codeEMFormula :: Set.Set SORT -> FORMULA EM_FORMULA -> FORMULA EM_FORMULA
codeEMFormula bsrts = foldFormula (codeRecord True bsrts $ codeEM bsrts)
