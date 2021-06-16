{- |
Module      :  ./ExtModal/ExtModal2Ship.hs
Description :  Translation from ExtModal to Ship
Copyright   :  (c) C. Maeder, DFKI GmbH 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable
-}

module ExtModal.ExtModal2Ship where

import CASL.AS_Basic_CASL
import CASL.Fold

import ExtModal.AS_ExtModal
import ExtModal.Ship

import qualified OWL2.AS as AS
import OWL2.ShipSyntax
import OWL2.Translate

import Common.Id
import Common.Result

transSid :: Token -> String
transSid = transString . show

transId :: Id -> String
transId = transString . show

toFoltl :: FORMULA EM_FORMULA -> Result Foltl
toFoltl = foldFormula foltlRec

foltlRec :: Record EM_FORMULA (Result Foltl) (Result Foltl)
foltlRec = (constRecord extModalToFoltlt (const $ fail "foltlRec1")
  (fail "foltlRec2"))
  { foldQuantification = \ _ q vs f _ -> if
      q == Unique_existential then fail "Unique_existential not supported"
      else fmap (PreOp $ QuantF
        (if q == Universal then AllValuesFrom else SomeValuesFrom)
        $ concatMap (\ (Var_decl l s _) -> map
                     (\ v -> AConcept (transSid v) . CName $ transId s) l) vs)
        f
  , foldJunction = \ _ j fs _ -> fmap (JoinedF
      $ if j == Con then IntersectionOf else UnionOf) $ sequence fs
  , foldRelation = \ _ mf1 r mf2 _ -> do
       f1 <- mf1
       f2 <- mf2
       let i = BinOp f1 Impl f2
       return $ if r == Equivalence then
           JoinedF IntersectionOf [i, BinOp f2 Impl f1]
           else i
  , foldNegation = \ _ f _ -> fmap (PreOp NotF) f
  , foldAtom = \ _ b _ -> return $ if b then trueFoltl else falseFoltl
  , foldPredication = \ (Predication ps as _) _ _ _ -> case as of
    [a] -> do
      n <- toNominal a
      return . ABoxass . AConcept n . CName $ predSymToString ps
    [a1, a2] -> do
      n1 <- toNominal a1
      n2 <- toNominal a2
      return . ABoxass . ARole n1 n2 . RName $ predSymToString ps
    _ -> fail "no concept or role"
  , foldDefinedness = \ _ _ _ -> fail "foltlRec.Definedness"
  , foldEquation = \ (Equation t1 _ t2 _) _ _ _ _ -> do
      s1 <- toNominal t1
      s2 <- toNominal t2
      return . ABoxass $ AIndividual s1 Same s2
  , foldMembership = \ (Membership t s _) _ _ _ -> do
      n <- toNominal t
      return . ABoxass . AConcept n . CName $ transId s
  , foldQuantOp = \ _ _ _ _ -> fail "foltlRec.QuantOp"
  , foldQuantPred = \ _ _ _ _ -> fail "foltlRec.QuantPred"
  }

extModalToFoltlt :: EM_FORMULA -> Result Foltl
extModalToFoltlt emf = case emf of
  PrefixForm p pf _ -> do
    f <- toFoltl pf
    case p of
      NextY True -> return $ PreOp X f
      StateQuantification True b -> return $ PreOp (if b then G else F) f
      _ -> fail "extModalToFoltl.PrefixForm"
  UntilSince True f1 f2 _ -> do
    u1 <- toFoltl f1
    u2 <- toFoltl f2
    return $ BinOp u1 Until u2
  _ -> fail "extModalToFoltl"

predSymToString :: PRED_SYMB -> String
predSymToString = transId . predSymbName

toNominal :: TERM EM_FORMULA -> Result String
toNominal trm = case trm of
  Qual_var v _ _ -> return . transString $ show v
  Sorted_term t _ _ -> toNominal t
  Cast t _ _ -> toNominal t
  _ -> fail "no nominal"
