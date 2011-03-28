{- |
Module      :  $Header$
Description :  converters for theories to MMiSSOntology
  (subsorting and concept taxonomies)
Copyright   :  (c) Klaus Luettich, Uni Bremen 2002-2004
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Converters for theories to MMiSSOntology (subsorting and concept taxonomies)

the functions showOntClass, showRelationName and showRelation may be used
for printing out MMiSS Ontologies in LaTeX to Stdout
(see commets marked with --printOut).
Please do not remove them without reason!!
-}

module CASL.Taxonomy
  ( -- * Conversion
    convTaxo
    -- * Printing of MMiSS ontologies in LaTeX
  , showOntClass, showRelationName, showRelation) where

import qualified Data.Map as Map
import qualified Common.Lib.Rel as Rel
import qualified Data.Set as Set

import CASL.AS_Basic_CASL
import CASL.Sign

import Taxonomy.MMiSSOntology

import Common.Taxonomy
import Common.Result
import Common.Id ()
import Common.AS_Annotation

{- | convert a generic CASL signature into the MMiSS ontology
datastructure for display as taxonomy graph -}
convTaxo :: TaxoGraphKind -> MMiSSOntology
         -> Sign f e
         -> [Named (FORMULA f)] -> Result MMiSSOntology
convTaxo kind onto sign sens =
   fromWithError $
   case kind of
    KSubsort -> convSign KSubsort onto sign
    KConcept -> foldl convSen (convSign KConcept onto sign) sens

convSign :: TaxoGraphKind
         -> MMiSSOntology -> Sign f e -> WithError MMiSSOntology
convSign KConcept o s =
    case convSign KSubsort o s of
    wOnto -> weither (const wOnto) (convPred s) wOnto
convSign KSubsort onto sign =
    Set.fold addSor (hasValue onto) $ sortSet sign
-- Ausgehend von den Top-Sorten -- Rel.mostRight

    where str = show
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
          toStrL = Set.fold ((:) . str) []

convPred :: Sign f e -> MMiSSOntology -> WithError MMiSSOntology
convPred s o =
    -- first only binary preds; later also unary preds
    Map.foldWithKey addPred (hasValue o) $ predMap s
    where addPred pn tSet wOnto =
           weither (const wOnto) insBinaryPred wOnto
           where insBinaryPred on =
                  let binT = Set.filter ((== 2) . length . predArgs) tSet
                  in if Set.null binT
                        then hasValue on
                        else Set.fold insType (insName on) binT
                 insName on = insertBaseRelation on (show pn) (show pn)
                                     Nothing Nothing
                 insType t wOn =
                     weither (const wOn)
                             (\ ont ->
                                 let [a1, a2] = predArgs t
                                     src = show a1
                                     tar = show a2
                                 in insertRelationType ont (show pn)
                                       src tar)
                             wOn

convSen :: WithError MMiSSOntology
        -> Named (FORMULA f) -> WithError MMiSSOntology
convSen weOnto _nSen = weither (const weOnto) hasValue weOnto

-- implemented but not used by now
showOntClass :: String -> [String] -> String
showOntClass cln =
    foldl (\ res sup -> res ++ ontClass sup) ""
    where ontClass s = "\\Class{" ++ cln ++ "}{" ++ cln ++ "}{" ++ s ++ "}"

showRelationName :: String -> String
showRelationName rn = "\\RelationName{" ++ rn ++ "}{" ++ rn ++ "}"

showRelation :: String -> String -> String -> String
showRelation rn s t = "\\Relation{" ++ rn ++ "}{" ++ s ++ "}{" ++ t ++ "}{}"
