

{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable 

This module provides converters for (Sign f e) and [Named (FORMULA f)] to MMiSSOntology

-}

module CASL.Taxonomy where

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.Set as Set

import CASL.AS_Basic_CASL
import CASL.Sign

import Taxonomy.MMiSSOntology

import Common.Taxonomy
import Common.Result
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
	     let sortStr = str sort in
	      weither (const weOnto)
		     (\ on -> 
		      maybe (insertClass on 
		                         sortStr sortStr 
			                 Nothing (Just SubSort))
	                     (\ l -> addSuperSorts sort l weOnto) $
		             Map.lookup sort relMap) weOnto
	  addSuperSorts sort supSl weOnto =
	      weither (const weOnto)
		     (\_ -> Set.fold insRel weOnto supSl) weOnto
	      where sortStr = str sort
		    insRel supS weOn =
			weither (const weOn)
			   (\ on -> 
			         insertClass on
			                     sortStr sortStr
			                     (Just (str supS))
			                     (Just SubSort)) weOn

convSen :: WithError MMiSSOntology 
	-> Named (FORMULA f) -> WithError MMiSSOntology
convSen weOnto _nSen = weither (const weOnto) hasValue weOnto
              -- insertClass (cSen nSen) o 

