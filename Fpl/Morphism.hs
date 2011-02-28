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
    BoolTerm t -> BoolTerm (rec t)

mapFunDef :: FplMor -> FunDef -> FunDef
mapFunDef m (FunDef i h@(Op_head k vs ms q) at r) =
   let nvs = map (mapVars m) vs
       nt = fmap (mapTerm mapTermExt m) at
   in maybe (FunDef i (Op_head k nvs ms q) nt r)
      (\ hty -> let
        (j, ty) = mapOpSym (sort_map m) (op_map m) (i, toOpType hty)
        in FunDef j (Op_head (opKind ty) nvs (fmap (mapSrt m) ms) q) nt r)
      $ headToType h
