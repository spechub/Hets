{-# LINE 1 "Propositional/AS_BASIC_Propositional.der.hs" #-}
{-# OPTIONS -fallow-undecidable-instances #-}
{- |
Module      :  $Header$
Description :  Instance of class Logic for propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@tzi.de
Stability   :  experimental
Portability :  portable

Simple rules for propositional logic
-}

{-
  Ref.
  http://en.wikipedia.org/wiki/Propositional_logic
-}

module Propositional.Rules
    (
     matImpl
    ,matEquiv
    ,matEquivImpl
    )
    where

import Propositional.AS_BASIC_Propositional as AS_BASIC
import Common.Id as Id
import Propositional.Sublogic as Sublogic

matImpl :: AS_BASIC.FORMULA -> AS_BASIC.FORMULA
matImpl (AS_BASIC.Implication f1 f2 rn) = 
    AS_BASIC.Disjunction [
                 (AS_BASIC.Negation (matImpl f1) Id.nullRange)
                , (matImpl f2)] rn
matImpl (AS_BASIC.Predication tok) = AS_BASIC.Predication tok
matImpl (AS_BASIC.Negation f rn)   = AS_BASIC.Negation (matImpl f) rn
matImpl (AS_BASIC.Conjunction f rn)   = AS_BASIC.Conjunction 
                                         (map matImpl f) rn
matImpl (AS_BASIC.Disjunction f rn)   = AS_BASIC.Disjunction 
                                         (map matImpl f) rn
matImpl (AS_BASIC.Equivalence f1 f2 rn) = 
    AS_BASIC.Equivalence (matImpl f1) (matImpl f2) rn
matImpl f = f

matEquiv :: AS_BASIC.FORMULA -> AS_BASIC.FORMULA
matEquiv (AS_BASIC.Equivalence f1 f2 rn) =
    let f1p = matEquiv f1
        f2p = matEquiv f2
    in
    AS_BASIC.Disjunction
            [
             AS_BASIC.Conjunction [f1p, f2p] Id.nullRange
            ,AS_BASIC.Conjunction [
              AS_BASIC.Negation f1p Id.nullRange
             ,AS_BASIC.Negation f2p Id.nullRange
             ] Id.nullRange
            ]
    rn
matEquiv (AS_BASIC.Predication tok) = AS_BASIC.Predication tok
matEquiv (AS_BASIC.Negation f rn)   = AS_BASIC.Negation (matImpl f) rn
matEquiv (AS_BASIC.Conjunction f rn)   = AS_BASIC.Conjunction 
                                         (map matImpl f) rn
matEquiv (AS_BASIC.Disjunction f rn)   = AS_BASIC.Disjunction 
                                         (map matImpl f) rn
matEquiv (AS_BASIC.Implication f1 f2 rn) = 
    AS_BASIC.Implication (matImpl f1) (matImpl f2) rn
matEquiv f = f

matEquivImpl :: AS_BASIC.FORMULA -> AS_BASIC.FORMULA
matEquivImpl (AS_BASIC.Implication f1 f2 rn) = 
    AS_BASIC.Disjunction [
                 (AS_BASIC.Negation (matEquivImpl f1) Id.nullRange)
                , (matEquivImpl f2)] rn
matEquivImpl (AS_BASIC.Equivalence f1 f2 rn) = 
    let f1p = matEquivImpl f1
        f2p = matEquivImpl f2
    in
    AS_BASIC.Disjunction
            [
             AS_BASIC.Conjunction [f1p, f2p] Id.nullRange
            ,AS_BASIC.Conjunction [
              AS_BASIC.Negation f1p Id.nullRange
             ,AS_BASIC.Negation f2p Id.nullRange
             ] Id.nullRange
            ]
    rn
matEquivImpl (AS_BASIC.Predication tok) = AS_BASIC.Predication tok
matEquivImpl (AS_BASIC.Negation f rn)   = AS_BASIC.Negation (matImpl f) rn
matEquivImpl (AS_BASIC.Conjunction f rn)   = AS_BASIC.Conjunction 
                                         (map matImpl f) rn
matEquivImpl (AS_BASIC.Disjunction f rn)   = AS_BASIC.Disjunction 
                                         (map matImpl f) rn
matEquivImpl f = f


