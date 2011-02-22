{- |
Module      :  $Header$
Description :  morphism mapping for FPL
Copyright   :  (c) Christian Maeder, DFKI GmbH 2011
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable
-}

module Fpl.Morphism (FplMor, mapFplSen) where

import Fpl.As
import Fpl.Sign

import CASL.Sign
import CASL.StaticAna
import CASL.AS_Basic_CASL
import CASL.Morphism
import CASL.MapSentence

type FplMor = Morphism TermExt SignExt (DefMorExt SignExt)

mapFplSen :: FplMor -> FplForm -> FplForm
mapFplSen = mapSen mapTermExt

mapTermExt :: FplMor -> TermExt -> TermExt
mapTermExt m te = let rec = mapTerm mapTermExt m in case te of
    FixDef fd -> FixDef $ mapFunDef m fd
    Case o l r -> Case (rec o) (map (\ (p, t) -> (rec p, rec t)) l) r
    Let fd t r -> Let (mapFunDef m fd) (rec t) r
    IfThenElse f t e r -> IfThenElse (rec f) (rec t) (rec e) r
    EqTerm t e r -> EqTerm (rec t) (rec e) r

mapFunDef :: FplMor -> FunDef -> FunDef
mapFunDef m (FunDef i h@(Op_head _ vs s q) at r) =
   let (j, ty) = mapOpSym (sort_map m) (op_map m) (i, toOpType $ headToType h)
   in FunDef j (Op_head (opKind ty) (map (mapVars m) vs) (mapSrt m s) q)
        (fmap (mapTerm mapTermExt m) at) r
