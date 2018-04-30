{- |
Module      :  ./RigidCASL/StaticAna.hs
Copyright   :  (c) M. Codescu, IMAR, 2018
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  mscodescu@gmail.com
Stability   :  provisional
Portability :  portable

static analysis of rigid parts
-}

module RigidCASL.StaticAna where

import RigidCASL.AS_Rigid
import RigidCASL.Print_AS ()
import RigidCASL.Sign

import CASL.Sign
import CASL.MixfixParser
import CASL.StaticAna
import CASL.AS_Basic_CASL
import CASL.Overload

import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Id
import Common.Result
import Common.ExtSign
import qualified Common.Lib.MapSet as MapSet
import Common.Lib.State

import qualified Data.Set as Set

import Debug.Trace

basicRigidAnalysis
  :: (R_BASIC_SPEC, RSign, GlobalAnnos)
  -> Result (R_BASIC_SPEC,
             ExtSign RSign Symbol,
             [Named CASLFORMULA])
basicRigidAnalysis = basicAnalysis typeAnaF anaRBasicItem anaRSigItem anaMix

typeAnaF :: Min () RigidExt
typeAnaF = const return

anaRBasicItem :: Ana () () R_SIG_ITEM () RigidExt
anaRBasicItem = const return

anaRSigItem :: Ana R_SIG_ITEM () R_SIG_ITEM () RigidExt
anaRSigItem mix ritem = do
  sig <- get
  case ritem of 
    Rigid_sorts al ps ->
        do ul <- mapM (ana_SORT_ITEM typeAnaF mix NonEmptySorts) al
           mapM_ (\aoi -> case item aoi of 
                            Sort_decl sdecls _ -> 
                              mapM_ (updateExtInfo . addRigidSort sig) sdecls
                            _ -> error "no subsorts or isos should be rigid")
                 ul
           return $ Rigid_sorts ul ps 
    Rigid_op_items al ps ->
        do ul <- mapM (ana_OP_ITEM typeAnaF mix) al
           mapM_ (\ aoi -> case item aoi of
                   Op_decl ops ty _ _ ->
                       mapM_ (updateExtInfo . addRigidOp sig (toOpType ty)) ops
                   Op_defn i par _ _ -> maybe (return ())
                       (\ ty -> updateExtInfo $ addRigidOp sig (toOpType ty) i)
                       $ headToType par) ul
           return $ Rigid_op_items ul ps
    Rigid_pred_items al ps ->
        do ul <- mapM (ana_PRED_ITEM typeAnaF mix) al
           mapM_ (\ aoi -> case item aoi of
                   Pred_decl ops ty _ ->
                       mapM_ (updateExtInfo . addRigidPred sig (toPredType ty)) ops
                   Pred_defn i (Pred_head args _) _ _ ->
                       updateExtInfo $ addRigidPred sig
                                (PredType $ sortsOfArgs args) i ) ul
           return $ Rigid_pred_items ul ps 

addRigidSort :: Sign () RigidExt -> Id -> RigidExt -> Result RigidExt
addRigidSort sig i ext = 
 let rsorts = rigidSorts ext
     ssorts = sortSet sig 
     extI = ext {rigidSorts = Set.insert i $ rigidSorts ext} 
 in 
  if Set.member i ssorts then Result [mkDiag Warning "redeclaring sort as rigid" i] $ Just extI
   else 
     if Set.member i rsorts then Result [mkDiag Hint "repeated rigid sort" i] $ Just ext
      else return extI

addRigidOp :: Sign () RigidExt -> OpType -> Id -> RigidExt -> Result RigidExt
addRigidOp sig ty i ext = let 
  rops = rigidOps ext
  ops = opMap sig
  extI = ext {rigidOps = MapSet.insert i ty $ rigidOps ext}
 in 
   if MapSet.member i ty ops then Result [mkDiag Warning "redeclaring op as rigid" i] $ Just extI 
    else
     if MapSet.member i ty rops then Result [mkDiag Hint "repeated rigid op" i] $ Just ext
      else return extI
          

addRigidPred :: Sign () RigidExt -> PredType -> Id -> RigidExt -> Result RigidExt
addRigidPred sig ty i ext = let 
  rpreds = rigidPreds ext
  preds = predMap sig
  extI = ext {rigidPreds = MapSet.insert i ty $ rigidPreds ext}
 in 
   if MapSet.member i ty preds then Result [mkDiag Warning "redeclaring pred as rigid" i] $ Just extI
   else if MapSet.member i ty rpreds then Result [mkDiag Hint "repeated rigid pred" i] $ Just ext
         else return extI

anaMix :: Mix () R_SIG_ITEM () RigidExt
anaMix = emptyMix



  {-               Min f e -- ^ type analysis of f
              -> Ana b b s f e  -- ^ static analysis of basic item b
              -> Ana s b s f e  -- ^ static analysis of signature item s
              -> Mix b s f e -- ^ for mixfix analysis
              -> (BASIC_SPEC b s f, Sign f e, GlobalAnnos)
                  BASIC_SPEC () R_SIG_ITEM ()

 b is ()
 s is R_SIG_ITEM
 f is ()
 e is RigidExt

type Ana a b s f e = Mix b s f e -> a -> State (Sign f e) a


-}
