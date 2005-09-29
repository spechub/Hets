

{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  portable 

This module provides converters for theories ((Sign f e) and [Named (FORMULA f)]) to MMiSSOntology

-}

module CASL.Taxonomy (convTaxo) where

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.Set as Set

import CASL.AS_Basic_CASL
import CASL.Sign

import Taxonomy.MMiSSOntology

import Common.Taxonomy
import Common.Result
import Common.PrettyPrint
import Common.AS_Annotation

convTaxo :: TaxoGraphKind -> MMiSSOntology
         -> Sign f e 
         -> [Named (FORMULA f)] -> Result MMiSSOntology
convTaxo kind onto sign sens =
   fromWithError $ 
   case kind of
    KSubsort -> convSign KSubsort onto sign
    KConcept -> foldl convSen (convSign KConcept onto sign) sens

convSign :: TaxoGraphKind -> 
            MMiSSOntology -> Sign f e -> WithError MMiSSOntology
convSign KConcept o s = convSign KSubsort o s
convSign KSubsort onto sign =
    Set.fold addSor (hasValue onto) $ sortSet sign
-- Ausgehend von den Top-Sorten -- Rel.mostRight

    --Map.foldWithKey addSort (hasValue onto) $ toMap $ sortRel sign
    where str x = showPretty x ""
          relMap = Rel.toMap $ Rel.intransKernel $ sortRel sign
          addSor sort weOnto =
             let sortStr = str sort 
             in weither (const weOnto)
                        (\ on -> insClass on sortStr
                                          (maybe [] toStrL $ 
                                                 Map.lookup sort relMap))
                        weOnto
          insClass o nm supL = 
              insertClass o nm nm supL (Just SubSort)
          toStrL = Set.fold (\ s rs -> str s : rs) [] 

convSen :: WithError MMiSSOntology 
        -> Named (FORMULA f) -> WithError MMiSSOntology
convSen weOnto _nSen = weither (const weOnto) hasValue weOnto
              -- insertClass (cSen nSen) o 

