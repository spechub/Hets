{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski and Uni Bremen 2003
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

   
   The embedding comorphism from CoCASL to Isabelle-HOL.

-}

{- todo: 
    encoding of cofreeness
    modal formulas
-}

module Comorphisms.CoCASL2IsabelleHOL where

import Logic.Logic
import Logic.Comorphism
import Data.List as List
import Data.Maybe
import Data.Char
import Debug.Trace
-- CoCASL
import CoCASL.Logic_CoCASL
import CoCASL.CoCASLSign
import CoCASL.AS_CoCASL
import CoCASL.StatAna
import CASL.AS_Basic_CASL
import CASL.Morphism
import Comorphisms.CASL2IsabelleHOL

-- Isabelle
import Isabelle.IsaSign as IsaSign
import Isabelle.Logic_Isabelle


-- | The identity of the comorphism
data CoCASL2IsabelleHOL = CoCASL2IsabelleHOL deriving (Show)

instance Language CoCASL2IsabelleHOL -- default definition is okay

instance Comorphism CoCASL2IsabelleHOL
               CoCASL ()
               C_BASIC_SPEC CoCASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CSign 
               CoCASLMor
               CASL.Morphism.Symbol CASL.Morphism.RawSymbol ()
               Isabelle () () IsaSign.Sentence () ()
               IsaSign.Sign 
               () () () ()  where
    sourceLogic _ = CoCASL
    sourceSublogic _ = ()
    targetLogic _ = Isabelle
    targetSublogic _ = ()
    map_theory _ = transTheory sigTrCoCASL formTrCoCASL
    --map_morphism _ morphism1 -> Maybe morphism2
    map_sentence _ sign =
      Just . mapSen formTrCoCASL sign
    --map_symbol :: cid -> symbol1 -> Set symbol2


-- | extended signature translation for CoCASL
sigTrCoCASL :: SignTranslator C_FORMULA CoCASLSign
sigTrCoCASL _ _ = id

-- | extended formula translation for CoCASL
formTrCoCASL :: FormulaTranslator C_FORMULA CoCASLSign
formTrCoCASL sign (CoSort_gen_ax sorts ops _) = 
  foldr (quantifyIsa "ALL") phi predDecls
  where
  phi = prems `binImpl` concls
  indices = [1..length sorts]
  predDecls = zip [rvar i | i<-indices] (map binPred sorts)
  binPred s = let s' = transSort s in [s',s'] ---> boolType
  prems = conj (map prem (zip sorts indices))
  prem (s::SORT,i) = 
    let sels = List.filter 
                (\(Qual_op_name _ t _) -> head (args_OP_TYPE t) == s) ops
        premSel opsymb@(Qual_op_name n t _) =
         let args = tail $ args_OP_TYPE t
             indicesArgs = [1..length args]
             res = res_OP_TYPE t
             varDecls = zip [xvar i | i<-indicesArgs] (map transSort args)
             top = Const (transOP_SYMB sign opsymb,dummyT)
             rhs = foldl App (top `App` var "x") (map (var . xvar) indicesArgs)
             lhs = foldl App (top `App` var "y") (map (var . xvar) indicesArgs)
             chi = if res `elem` sorts
                     then var (rvar (fromJust (findIndex (==res) sorts)))
                           `App` rhs `App` lhs
                     else binEq rhs lhs
          in foldr (quantifyIsa "ALL") chi varDecls
        prem1 = conj (map premSel sels)
        concl1 = var (rvar i) `App` var "x" `App` var "y"
        psi = prem1 `binImpl` concl1
        typS = transSort s
     in foldr (quantifyIsa "ALL") psi [("x",typS),("y",typS)]
  concls = conj (map concl (zip sorts indices))
  concl (s,i::Int) = binEq (var (rvar i)) (Const("op =",dummyT))
formTrCoCASL sign (Box mod phi _) = 
   trace "WARNING: ignoring modal forumla" 
          $ true
formTrCoCASL sign (Diamond mod phi _) = 
   trace "WARNING: ignoring modal forumla" 
          $ true
