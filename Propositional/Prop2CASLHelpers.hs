{- |
Module      :  $Header$
Description :  Helper functions for Prop2CASL
Copyright   :  (c) Dominik Luecke and Uni Bremen 2007
License     :  GPLv2 or higher

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable (imports Logic.Logic)

The helpers for translating comorphism from Propositional to CASL.

-}

module Propositional.Prop2CASLHelpers
    where

import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Common.AS_Annotation as AS_Anno
import qualified Common.Id as Id
import qualified Common.Result as Result

-- Propositional
import qualified Propositional.AS_BASIC_Propositional as PBasic
import qualified Propositional.Sublogic as PSL
import qualified Propositional.Sign as PSign
import qualified Propositional.Morphism as PMor
import qualified Propositional.Symbol as PSymbol

-- CASL
import qualified CASL.AS_Basic_CASL as CBasic
import qualified CASL.Sublogic as CSL
import qualified CASL.Sign as CSign
import qualified CASL.Morphism as CMor

-- | Translation of the signature
mapSig :: PSign.Sign -> CSign.CASLSign
mapSig sign = (CSign.emptySign ())
              {CSign.predMap = Set.fold (\x -> Map.insert x
                                (Set.singleton $ CSign.PredType
                                 {CSign.predArgs = []}))
                                Map.empty $ PSign.items sign }

-- | Which is the target sublogic?
mapSub :: PSL.PropSL -> CSL.CASL_Sublogics
mapSub sl =
    case (PSL.isHC sl) of
      True -> CSL.bottom
              { CSL.cons_features = CSL.NoSortGen
              , CSL.sub_features = CSL.NoSub
              , CSL.has_pred = True
              , CSL.has_eq = False
              , CSL.which_logic = CSL.Horn
              }
      False -> CSL.bottom
              { CSL.cons_features = CSL.NoSortGen
              , CSL.sub_features = CSL.NoSub
              , CSL.has_pred = True
              , CSL.has_eq = False
              , CSL.which_logic = CSL.FOL
              }

-- | Translation of morphisms
mapMor :: PMor.Morphism -> Result.Result CMor.CASLMor
mapMor mor = Result.Result [] $ Just (CMor.embedMorphism ()
    (mapSig $ PMor.source mor) $ mapSig $ PMor.target mor)
    { CMor.pred_map = trMor $ PMor.propMap mor }

-- | Mapping of a theory
mapTheory :: (PSign.Sign, [AS_Anno.Named (PBasic.FORMULA)])
  -> Result.Result (CSign.CASLSign, [AS_Anno.Named (CBasic.CASLFORMULA)])
mapTheory (sig, form) = Result.Result [] $
    Just (mapSig sig, map trNamedForm form)

-- | Translation of symbols
mapSym :: PSymbol.Symbol -> Set.Set CSign.Symbol
mapSym sym = Set.singleton $
    CSign.idToPredSymbol (PSymbol.symName sym) $ CSign.PredType []

-- | Translation of sentence
mapSentence :: PSign.Sign -> PBasic.FORMULA -> Result.Result CBasic.CASLFORMULA
mapSentence _ form = Result.Result [] $ Just $ trForm form

-------------------------------------------------------------------------------
-- Helpers                                                                   --
-------------------------------------------------------------------------------

-- | Helper for map theory
trNamedForm :: AS_Anno.Named (PBasic.FORMULA)
            -> AS_Anno.Named (CBasic.CASLFORMULA)
trNamedForm form = AS_Anno.mapNamed trForm form

-- | Helper for map sentence and map theory
trForm :: PBasic.FORMULA -> CBasic.CASLFORMULA
trForm form =
      case form of
        PBasic.Negation fn rn ->  CBasic.Negation (trForm fn) rn
        PBasic.Conjunction fn rn -> CBasic.Conjunction (map trForm fn) rn
        PBasic.Disjunction fn rn -> CBasic.Disjunction (map trForm fn) rn
        PBasic.Implication f1 f2 rn ->
                CBasic.Implication (trForm f1) (trForm f2) True rn
        PBasic.Equivalence f1 f2 rn ->
                CBasic.Equivalence (trForm f1) (trForm f2) rn
        PBasic.True_atom rn -> CBasic.True_atom rn
        PBasic.False_atom rn -> CBasic.False_atom rn
        PBasic.Predication pid -> CBasic.Predication
                                 (CBasic.Qual_pred_name (Id.simpleIdToId pid)
                                        (CBasic.Pred_type [] Id.nullRange)
                                        Id.nullRange
                                 )
                                 [] Id.nullRange

-- | Helper for map mor
trMor :: Map.Map Id.Id Id.Id -> Map.Map (Id.Id, CSign.PredType) Id.Id
trMor mp =
    let
        pt = CSign.PredType{CSign.predArgs = []}
    in
      Map.foldWithKey
             (\ k a ->
              Map.insert (k, pt) a
             )
      Map.empty
      mp
