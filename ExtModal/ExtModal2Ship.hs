{- |
Module      :  $Header$
Description :  Translation from ExtModal to Ship
Copyright   :  (c) C. Maeder, DFKI GmbH 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable
-}

module ExtModal.ExtModal2Ship where

import CASL.AS_Basic_CASL
import CASL.Sign

import ExtModal.AS_ExtModal
import ExtModal.ExtModalSign
import ExtModal.Ship

import OWL2.ShipSyntax
import OWL2.Translate

import Common.Result

data ABoxForm
  = ABoxForm Junctor [ABoxForm]
  | ABoxLit Bool ABox   -- False indicates negation
  deriving (Show, Eq, Ord)

data ABoxQuant = ABoxQuant (Maybe (Bool, [String])) ABoxForm
                 -- True indicates forall, the strings are individuals
  deriving (Show, Eq, Ord)

data ShipResult
  = ABoxAss ABoxQuant
  | ShipM Monitor
  | ShipResult Ship
  | Unprocessed (Result (FORMULA EM_FORMULA))

transSen :: Sign EM_FORMULA EModalSign -> FORMULA EM_FORMULA -> ShipResult
transSen _sig = Unprocessed . return

toABoxQuant :: FORMULA EM_FORMULA -> Result ABoxQuant
toABoxQuant frm = case frm of
  Quantification q vs f _ | q /= Unique_existential ->
    fmap (ABoxQuant
      $ Just (q == Universal
            , concatMap (\ (Var_decl l _ _) -> map (transString . show) l) vs))
    $ toABoxForm f
  _ -> fmap (ABoxQuant Nothing) $ toABoxForm frm

predSymToString :: PRED_SYMB -> String
predSymToString = transString . show . predSymbName

toABoxForm :: FORMULA EM_FORMULA -> Result ABoxForm
toABoxForm frm = case frm of
  Junction j fs _ -> fmap (ABoxForm j) $ mapM toABoxForm fs
  Predication ps as _ -> case as of
    [a] -> do
      n <- toNominal a
      return . ABoxLit True . AConcept n . CName $ predSymToString ps
    [a1, a2] -> do
      n1 <- toNominal a1
      n2 <- toNominal a2
      return . ABoxLit True . ARole n1 n2 . RName $ predSymToString ps
    _ -> fail "no concept or role"
  _ -> fail "no abox formula"

toNominal :: TERM EM_FORMULA -> Result String
toNominal trm = case trm of
  Qual_var v _ _ -> return . transString $ show v
  Sorted_term t _ _ -> toNominal t
  Cast t _ _ -> toNominal t
  _ -> fail "no nominal"
