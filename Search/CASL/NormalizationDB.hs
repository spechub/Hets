{- |
Module      :  $Header$
Description :  A in memory database for normalized CASL formulae
Copyright   :  (c) Immanuel Normann, Uni Bremen 2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  inormann@jacobs-university.de
Stability   :  provisional
Portability :  portable
-}
module Search.CASL.NormalizationDB where

import CASL.FormulaWrapper
import Search.Common.Normalization
import qualified Data.Map as Map
import OMDoc.HetsInterface
import Search.Common.AS_Annotation -- (senName)

getSentence dg node nr = sentence ((getNodeSentences (getNodeByNr dg node))!!nr)

{-mapWithKey :: (k -> a -> b) -> Map k a -> Map k b

myCasls =  "~/programming/my-src/casl/"
dg <- getDG "./Basic/Numbers.casl"
let s = getSentence dg 0

:module +CASL.FormulaWrapper
normalizeCaslFormula $ s 0

let sens = map (getSentence dg 0) [0..60]


let n = getNodeByNr dg
let sens = getNodeSentences (n 0)
let s nr = sentence (sens!!nr)


updateDB db filePath= 
    where dg = getDG filePath
          sens = getSentencesWithNodeNames
sen = senName
          nf = normalizeCaslFormula sen

let sm = getSentencesWithNodeNames dg
let (Just n) = Map.lookup "DecimalFraction_1" sm
s = Data.Set.findMin n
Common.AS_Annotation.senName s
Common.AS_Annotation.sentence s

-}