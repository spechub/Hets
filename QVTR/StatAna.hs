{- |
Module      :  $Header$
Description :  Static QVTR analysis
Copyright   :  (c) Daniel Calegari Universidad de la Republica, Uruguay 2013
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  dcalegar@fing.edu.uy
Stability   :  provisional
Portability :  portable
-}

module QVTR.StatAna where

import QVTR.As
import QVTR.Sign

import qualified CSMOF.As as CSMOFAs
import qualified CSMOF.Sign as CSMOFSign
import qualified CSMOF.StatAna as CSMOFStatAna

import Common.Result
import Common.GlobalAnnotations
import Common.ExtSign
import Common.AS_Annotation

import qualified Data.Map as Map


basicAna :: (Transformation, Sign, GlobalAnnos) -> Result (Transformation, ExtSign Sign (), [Named Sen])
basicAna (trans, _, _) = return (trans, mkExtSign (buildSignature trans), buildSentences trans)


buildSignature :: Transformation -> Sign
buildSignature (Transformation _ souMet tarMet _ rels) = 
  let 
    souMetSign = CSMOFStatAna.buildSignature (third souMet)
    tarMetSign = CSMOFStatAna.buildSignature (third tarMet)
    relat = buildRelations souMetSign tarMetSign rels
  in
    Sign { sourceSign = souMetSign
         , targetSign = tarMetSign
         , nonTopRelations = fst relat
         , topRelations = snd relat
         }


buildRelations :: CSMOFSign.Sign -> CSMOFSign.Sign -> [Relation] -> (Map.Map String RuleDef,Map.Map String RuleDef)
buildRelations _ _ _ = (Map.empty,Map.empty) -- ToDo
--souMetSign tarMetSign relations

buildSentences :: Transformation -> [Named Sen]
buildSentences (Transformation _ _ _ kes _) = -- (Transformation _ souMet tarMet kes rels) =
  let 
    keyConstr = buildKeyConstr kes
    qvtRules = [] -- buildRules rels
  in
    keyConstr ++ qvtRules


buildKeyConstr :: [Key] -> [Named Sen]
buildKeyConstr [] = []
buildKeyConstr (k : rest) = (buildKeyC k) : buildKeyConstr rest

buildKeyC :: Key -> Named Sen
buildKeyC k = makeNamed "" (KeyConstr { keyConst = k}) --ToDo

third :: (String,String,CSMOFAs.Metamodel) -> CSMOFAs.Metamodel
third (_, _, c) = c
