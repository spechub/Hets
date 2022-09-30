{- |
Module      :  ./RigidCASL/StaticAna.hs
Copyright   :  (c) R. Diaconescu, IMAR, 2018
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
import RigidCASL.Morphism

import CASL.Sign
import CASL.Morphism
import CASL.MixfixParser
import CASL.StaticAna
import CASL.AS_Basic_CASL
import CASL.Overload
import CASL.ColimSign
import CASL.Logic_CASL

import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Id
import Common.Result
import Common.ExtSign
import qualified Common.Lib.MapSet as MapSet
import Common.Lib.State
import qualified Common.Lib.Graph as Gr
import Data.Graph.Inductive.Graph

import qualified Data.Set as Set
import Logic.SemConstr
import Data.List
import qualified Data.Map as Map

basicRigidAnalysis
  :: (R_BASIC_SPEC, RSign, GlobalAnnos)
  -> Result (R_BASIC_SPEC,
             ExtSign RSign Symbol,
             [Named CASLFORMULA])
basicRigidAnalysis = basicAnalysis typeAnaF anaRBasicItem anaRSigItem anaMix

basicRigidAnalysis'
  :: (R_BASIC_SPEC, RSign, GlobalAnnos)
  -> Result (R_BASIC_SPEC,
             ExtSign RSign RigidSymbol,
             [Named CASLFORMULA])
basicRigidAnalysis' (rbs, rsig, ga) = do
 (rbs', ExtSign sig syms, nsens) <- basicAnalysis typeAnaF anaRBasicItem anaRSigItem anaMix (rbs, rsig, ga)
 return (rbs', ExtSign sig (Set.map CSym syms), nsens) -- TODO: this is wrong but may do for now. Need to make rigid symbols rigid in ExtSign also

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

-- | extra
rigidCASLsen_analysis ::
        (R_BASIC_SPEC, RSign, FORMULA()) -> Result (FORMULA (), FORMULA ())
rigidCASLsen_analysis (bs, s, f) = let
                         mix = emptyMix
                         allIds = getAllIds bs mix s
                         mix' = mix { mixRules = makeRules emptyGlobalAnnos
                                                           allIds }
                         in anaForm (const return) mix' (caslSign s) f

sigColim     :: Gr.Gr RSign (Int, RigidMor)
             -> Result
                  (RSign, Map.Map Int RigidMor)
sigColim gr = do
 let cgr = emap (\(i,m) -> (i, caslMor m)) $ nmap caslSign gr
     (csig, cmors) = signColimit cgr extCASLColimit
     sortExt = foldl (\aSet (i,iSig) -> Set.union 
                                       aSet $ 
                                       Set.map (\x -> let iMor = Map.findWithDefault (error "morphism not found") i cmors
                                                      in Map.findWithDefault x x $ sort_map iMor)
                  $ rigidSorts $ extendedInfo iSig ) Set.empty $ labNodes gr
     opsExt = foldl (\aMap (i, iSig) -> let iMor = Map.findWithDefault (error "morphism not found") i cmors
                                            sMap = sort_map iMor
                                            oMap = op_map iMor
                                        in
                                         foldl (\f (sn,ot) -> MapSet.insert sn ot f) aMap $
                                         map (mapOpSym sMap oMap) $
                                         MapSet.toPairList $ rigidOps $ extendedInfo iSig
                    )  
               MapSet.empty $ labNodes gr
     predExt = foldl (\aMap (i, iSig) -> let iMor = Map.findWithDefault (error "morphism not found") i cmors
                                             sMap = sort_map iMor
                                             pMap = pred_map iMor
                                         in foldl (\f (sn,ot) -> MapSet.insert sn ot f) aMap $
                                             map (mapPredSym sMap pMap) $
                                             MapSet.toPairList $ rigidPreds $ extendedInfo iSig
                     )
                MapSet.empty $ labNodes gr
     rext = RigidExt sortExt opsExt predExt
     rsign = toRSign csig rext
     -- TODO: rigid ops, rigid preds, morphisms
 return (rsign, Map.fromList $ 
                map (\(i, rsig) -> let iMor = Map.findWithDefault (error "morphism not found") i cmors 
                                   in (i, toRigidMor iMor (extendedInfo rsig) rext)
                    ) $ labNodes gr)
 

-- | CASL hybridization: constraints to CASL sentences

rigidConstrToSens :: Sign () RigidExt -> String -> SemanticConstraint -> Result [Named (FORMULA ())]
rigidConstrToSens sig str sc = -- TODO: add a String argument so the error message is different for RigidCASL and CASL
 let 
   st = genName $ "ST_" ++ str
   domain = genName $ "domain_" ++ str
   defined = genName "defined"
   (totals, partials) = partition (\(_, ot) -> opKind ot == Total) $ MapSet.toPairList $ rigidOps $ extendedInfo sig
 in
 case sc of
  {-SameInterpretation "sort" -> 
    return $
    map (\s -> makeNamed ("ga_sem_constr_"++show s)
                $ mkForall [mkVarDecl (genToken "w1") st, 
                            mkVarDecl (genToken "w2") st, 
                            mkVarDecl (genToken "x") s]
                $ mkEqv 
                  (mkPredication (mkQualPred domain $ Pred_type [st, s] nullRange)
                                 [Qual_var (genToken "w1") st nullRange,
                                  Qual_var (genToken "x") s nullRange])
                  (mkPredication (mkQualPred domain $ Pred_type [st, s] nullRange)
                                 [Qual_var (genToken "w2") st nullRange,
                                  Qual_var (genToken "x") s nullRange]) 
          ) 
                $ Set.toList $ sortSet sig-}
  SameInterpretation "rigid sort" -> 
    return $
    map (\s -> makeNamed ("ga_sem_constr_"++show s)
                $ mkForall [mkVarDecl (genToken "w1") st, 
                            mkVarDecl (genToken "w2") st, 
                            mkVarDecl (genToken "x") s]
                $ mkEqv 
                  (mkPredication (mkQualPred domain $ Pred_type [st, s] nullRange)
                                 [Qual_var (genToken "w1") st nullRange,
                                  Qual_var (genToken "x") s nullRange])
                  (mkPredication (mkQualPred domain $ Pred_type [st, s] nullRange)
                                 [Qual_var (genToken "w2") st nullRange,
                                  Qual_var (genToken "x") s nullRange]) 
          ) 
                $ Set.toList $ rigidSorts $ extendedInfo sig
  SameInterpretation "rigid const" -> error "nyi for rigid const"
  SameInterpretation "rigid op" ->
   let
      xs ot = zip (opArgs ot) [1::Int ..]
      extOt i ot = Qual_op_name i (Op_type Total (st:opArgs ot) (opRes ot) nullRange) nullRange
    in return $
        map (\(i,ot) -> makeNamed ("ga_sem_constr_" ++ show i)
                $ mkForall 
                                ( [mkVarDecl (genToken "w1") st, 
                                   mkVarDecl (genToken "w2") st]
                                  ++ 
                                  (map (\(si, ii) -> mkVarDecl (genToken $ "x" ++ show ii) si) $ xs ot)
                                 ) 
                                 $ mkStEq 
                                      (mkAppl (extOt i ot) $ map (\(a,b) -> mkVarTerm a b) $ (genToken "w1", st):(map (\(si, ii) -> (genToken $ "x" ++ show ii, si)) $ xs ot))
                                      (mkAppl (extOt i ot) $ map (\(a,b) -> mkVarTerm a b) $ (genToken "w2", st):(map (\(si, ii) -> (genToken $ "x" ++ show ii, si)) $ xs ot))
          ) totals
  {-SameInterpretation "pred" ->
    let
      xs pt = zip (predArgs pt) [1::Int ..]  
      extPt (Pred_type ss r) = Pred_type (st:ss) r 
    in return $
        map (\(i, pt) -> makeNamed ("ga_sem_constr_" ++ show i) $ 
                          mkForall 
                           ( [mkVarDecl (genToken "w1") st, 
                              mkVarDecl (genToken "w2") st]
                              ++ 
                              (map (\(si, ii) -> mkVarDecl (genToken $ "x" ++ show ii) si) $ xs pt)
                           )
                           $ mkEqv (mkPredication (mkQualPred i $ extPt $ toPRED_TYPE pt) $ 
                                     map (\(a,b) -> mkVarTerm a b) $ (genToken "w1", st):(map (\(si, ii) -> (genToken $ "x" ++ show ii, si)) $ xs pt))
                                   (mkPredication (mkQualPred i $ extPt $ toPRED_TYPE pt) $
                                     map (\(a,b) -> mkVarTerm a b) $ (genToken "w2", st):(map (\(si, ii) -> (genToken $ "x" ++ show ii, si)) $ xs pt)) 
            ) $ MapSet.toPairList $ predMap sig -}
  SameInterpretation "rigid pred" ->
    let
      xs pt = zip (predArgs pt) [1::Int ..]  
      extPt (Pred_type ss r) = Pred_type (st:ss) r 
    in return $
        map (\(i, pt) -> makeNamed ("ga_sem_constr_" ++ show i) $ 
                          mkForall 
                           ( [mkVarDecl (genToken "w1") st, 
                              mkVarDecl (genToken "w2") st]
                              ++ 
                              (map (\(si, ii) -> mkVarDecl (genToken $ "x" ++ show ii) si) $ xs pt)
                           )
                           $ mkEqv (mkPredication (mkQualPred i $ extPt $ toPRED_TYPE pt) $ 
                                     map (\(a,b) -> mkVarTerm a b) $ (genToken "w1", st):(map (\(si, ii) -> (genToken $ "x" ++ show ii, si)) $ xs pt))
                                   (mkPredication (mkQualPred i $ extPt $ toPRED_TYPE pt) $
                                     map (\(a,b) -> mkVarTerm a b) $ (genToken "w2", st):(map (\(si, ii) -> (genToken $ "x" ++ show ii, si)) $ xs pt)) 
            ) $ MapSet.toPairList $ rigidPreds $ extendedInfo sig
  SameDomain True -> let
      xs ot = zip (opArgs ot) [1::Int ..]
      extOt i ot = Qual_op_name i (Op_type Total (st:opArgs ot) (opRes ot) nullRange) nullRange
    in return $
     map (\(i,ot) -> makeNamed ("ga_sem_constr_" ++ show i)
                $ mkForall 
                                ( [mkVarDecl (genToken "w1") st, 
                                   mkVarDecl (genToken "w2") st]
                                  ++ 
                                  (map (\(si, ii) -> mkVarDecl (genToken $ "x" ++ show ii) si) $ xs ot)
                                 ) 
                                 $ mkEqv 
                                      (mkPredication (mkQualPred defined $ Pred_type [st, opRes ot] nullRange) $ 
                                       [mkVarTerm (genToken "w1") st,
                                        mkAppl (extOt i ot) $ map (\(a,b) -> mkVarTerm a b) $ (genToken "w1", st):(map (\(si, ii) -> (genToken $ "x" ++ show ii, si)) $ xs ot)
                                       ]
                                       )
                                      (mkPredication (mkQualPred defined $ Pred_type [st, opRes ot] nullRange) $ 
                                       [mkVarTerm (genToken "w2") st,
                                        mkAppl (extOt i ot) $ map (\(a,b) -> mkVarTerm a b) $ (genToken "w2", st):(map (\(si, ii) -> (genToken $ "x" ++ show ii, si)) $ xs ot)
                                       ]
                                       )
          ) 
                partials 
  _ -> constrToSens (caslSign sig) str sc -- error $ "Constraint not supported for CASL logic:" ++ show sc  
