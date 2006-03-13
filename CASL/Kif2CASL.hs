{- |
Module      :  $Header$
Copyright   :  (c) T.Mossakowski, C.Maeder and Uni Bremen 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

Parsing lists of lists being MILO (MId-Level Ontology) .kif files
-}

module CASL.KifCASL where

import Common.Id
import CASL.Kif
import CASL.AS_Basic_CASL

-- data StringKind = Quoted | Token | QWord
-- data ListOfList = Literal StringKind String | List [ListOfList]

--| 
universe :: SORT
universe = undefined

kif2CASLFormula :: ListOfList -> FORMULA () ()
kif2CASLFormula (List (Token "and" : phis)) =
  Conjunction (map kif2CASLFormula phis) nullRange
kif2CASLFormula (List (Token "or" : phis)) =
  Disjunction (map kif2CASLFormula phis) nullRange
kif2CASLFormula (List [Token "=>", phi1, phi2]) =
  Implication (kif2CASLFormula phi1) (kif2CASLFormula phi2) True nullRange
kif2CASLFormula (List [Token "<=>", phi1, phi2]) =
  Equivalence (kif2CASLFormula phi1) (kif2CASLFormula phi2) nullRange
kif2CASLFormula (List [Token "True"]) =
  True_atom nullRange
kif2CASLFormula (List [Token "False"]) =
  False_atom nullRange
kif2CASLFormula (List [Token "exists", varList, phi]) =
  Quantification Existential (kif2CASLvarList varList) (kif2CASLFormula phi) nullRange
kif2CASLFormula (List [Token "forall", varList, phi]) =
  Quantification Universal (kif2CASLvarList varList) (kif2CASLFormula phi) nullRange


kif2CASL :: [ListOfList] -> (Sign () (),[Named (FORMULA () ())])
kif2CASL = undefined