{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  Extension of CFOL2IsabelleHOL to CoCASL
Copyright   :  (c) Till Mossakowski and Uni Bremen 2003-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  hausmann@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The embedding comorphism from CoCASL to Isabelle-HOL.
-}

module Comorphisms.CoCFOL2IsabelleHOL (CoCFOL2IsabelleHOL (..)) where

import Logic.Logic as Logic
import Logic.Comorphism
-- CoCASL
import CoCASL.Logic_CoCASL
import CoCASL.CoCASLSign
import CoCASL.AS_CoCASL
import CoCASL.StatAna
import CoCASL.Sublogic

import CASL.Sublogic as SL
import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism

import Comorphisms.CFOL2IsabelleHOL

-- Isabelle
import Isabelle.IsaSign as IsaSign
import Isabelle.IsaConsts
import Isabelle.Logic_Isabelle

import Common.Utils (number)

import Data.Char (ord, chr)
import Data.Maybe (fromMaybe)

-- | The identity of the comorphism
data CoCFOL2IsabelleHOL = CoCFOL2IsabelleHOL deriving Show

instance Language CoCFOL2IsabelleHOL where
  language_name CoCFOL2IsabelleHOL = "CoCASL2Isabelle"

instance Comorphism CoCFOL2IsabelleHOL
               CoCASL CoCASL_Sublogics
               C_BASIC_SPEC CoCASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CSign
               CoCASLMor
               Symbol RawSymbol ()
               Isabelle () () IsaSign.Sentence () ()
               IsaSign.Sign
               IsabelleMorphism () () () where
    sourceLogic CoCFOL2IsabelleHOL = CoCASL
    sourceSublogic CoCFOL2IsabelleHOL = SL.cFol
    targetLogic CoCFOL2IsabelleHOL = Isabelle
    mapSublogic cid sl = if sl `isSubElem` sourceSublogic cid
                       then Just () else Nothing
    map_theory CoCFOL2IsabelleHOL =
      return . transTheory sigTrCoCASL formTrCoCASL
    map_sentence CoCFOL2IsabelleHOL sign =
      return . mapSen formTrCoCASL sign (typeToks sign)
    has_model_expansion CoCFOL2IsabelleHOL = True
    is_weakly_amalgamable CoCFOL2IsabelleHOL = True

xvar :: Int -> String
xvar i = if i <= 26 then [chr (i + ord 'a')] else 'x' : show i

rvar :: Int -> String
rvar i = if i <= 9 then [chr (i + ord 'R' )] else 'R' : show i

-- | extended signature translation for CoCASL
sigTrCoCASL :: SignTranslator C_FORMULA CoCASLSign
sigTrCoCASL _ _ = id

conjs :: [Term] -> Term
conjs l = if null l then true else foldr1 binConj l

-- | extended formula translation for CoCASL
formTrCoCASL :: FormulaTranslator C_FORMULA CoCASLSign
formTrCoCASL sign tyToks (CoSort_gen_ax sorts ops _) =
  foldr (quantifyIsa "All") phi $ predDecls ++ [("u", ts), ("v", ts)]
  where
  ts = transSort $ head sorts
  -- phi expresses: all bisimulations are the equality
  phi = prems `binImpl` concls
  -- indices and predicates for all involved sorts
  indexedSorts = number sorts
  predDecls = map (\ (s, i) -> (rvar i, binPred s)) indexedSorts
  binPred s = let s' = transSort s in mkCurryFunType [s', s'] boolType
  -- premises: all relations are bisimulations
  prems = conjs (map prem indexedSorts)
  {- generate premise for s, where s is the i-th sort
     for all x,y of that sort,
      if all sel_j(x) R_j sel_j(y), where sel_j ranges over the selectors for s
      then x R y
     here, R_i is the relation for the result type of sel_j, or the equality
  -}
  prem (s, i) =
    let -- get all selectors with first argument sort s
        sels = filter isSelForS ops
        isSelForS (Qual_op_name _ t _) = case args_OP_TYPE t of
           s1 : _ -> s1 == s
           _ -> False
        isSelForS _ = False
        premSel opsymb@(Qual_op_name _n t _) =
         let -- get extra parameters of the selectors
             args = tail $ args_OP_TYPE t
             indicesArgs = number args
             res = res_OP_TYPE t
             -- variables for the extra parameters
             varDecls = map (\ (a, j) -> (xvar j, transSort a))
                        indicesArgs
             -- the selector ...
             topC = con (transOpSymb sign tyToks opsymb)
             -- applied to x and extra parameter vars
             appFold = foldl termAppl
             rhs = appFold (termAppl topC $ mkFree "x")
                       $ map (mkFree . xvar . snd) indicesArgs
             -- applied to y and extra parameter vars
             lhs = appFold (termAppl topC $ mkFree "y")
                             $ map (mkFree . xvar . snd) indicesArgs
             chi = -- is the result of selector non-observable?
                   if res `elem` sorts
                     -- then apply corresponding relation
                     then termAppl (termAppl (mkFree $
                          rvar $ fromMaybe
                                   (error "CoCASL2Isabelle.premSel.chi")
                               $ lookup res indexedSorts )
                               rhs) lhs
                     -- else use equality
                     else binEq rhs lhs
          in foldr (quantifyIsa "All") chi varDecls
        premSel _ = error "CoCASL2Isabelle.premSel"
        prem1 = conjs (map premSel sels)
        concl1 = termAppl (termAppl (mkFree $ rvar i) $ mkFree "x")
                 (mkFree "y")
        psi = concl1 `binImpl` prem1
        typS = transSort s
     in foldr (quantifyIsa "All") psi [("x", typS), ("y", typS)]
  -- conclusion: all relations are the equality
  concls = conjs (map concl indexedSorts)
  concl (_, i) = binImpl (termAppl (termAppl (mkFree $ rvar i) $ mkFree "u")
                     $ mkFree "v")
                             $ binEq (mkFree "u") $ mkFree "v"
formTrCoCASL _sign _ (BoxOrDiamond _ _mod _phi _) =
    error "CoCFOL2IsabelleHOL.formTrCoCASL.BoxOrDiamond"
