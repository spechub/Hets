{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2004-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

static analysis of modal logic parts
-}

module Modal.StatAna (basicModalAnalysis, minExpForm) where

import Modal.AS_Modal
import Modal.Print_AS ()
import Modal.ModalSign

import CASL.Sign
import CASL.MixfixParser
import CASL.StaticAna
import CASL.AS_Basic_CASL
import CASL.ShowMixfix
import CASL.Overload
import CASL.Quantification

import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Keywords
import qualified Data.Map as Map
import qualified Data.Set as Set
import Common.Lib.State
import Common.Id
import Common.Result
import Common.ExtSign
import Data.List as List

instance TermExtension M_FORMULA where
    freeVarsOfExt sign (BoxOrDiamond _ _ f _) = freeVars sign f

basicModalAnalysis
  :: (BASIC_SPEC M_BASIC_ITEM M_SIG_ITEM M_FORMULA,
      Sign M_FORMULA ModalSign, GlobalAnnos)
  -> Result (BASIC_SPEC M_BASIC_ITEM M_SIG_ITEM M_FORMULA,
             ExtSign (Sign M_FORMULA ModalSign) Symbol,
             [Named (FORMULA M_FORMULA)])
basicModalAnalysis =
    basicAnalysis minExpForm ana_M_BASIC_ITEM ana_M_SIG_ITEM ana_Mix

ana_Mix :: Mix M_BASIC_ITEM M_SIG_ITEM M_FORMULA ModalSign
ana_Mix = emptyMix
    { getSigIds = ids_M_SIG_ITEM
    , putParen = mapM_FORMULA
    , mixResolve = resolveM_FORMULA
    }

-- rigid ops will also be part of the CASL signature
ids_M_SIG_ITEM :: M_SIG_ITEM -> IdSets
ids_M_SIG_ITEM si = let e = Set.empty in case si of
    Rigid_op_items _ al _ ->
        (unite2 $ map (ids_OP_ITEM . item) al, e)
    Rigid_pred_items _ al _ ->
        ((e, e), Set.unions $ map (ids_PRED_ITEM . item) al)

mapMODALITY :: MODALITY -> MODALITY
mapMODALITY m = case m of
    Term_mod t -> Term_mod $ mapTerm mapM_FORMULA t
    _ -> m

mapM_FORMULA :: M_FORMULA -> M_FORMULA
mapM_FORMULA (BoxOrDiamond b m f ps) =
    BoxOrDiamond b (mapMODALITY m) (mapFormula mapM_FORMULA f) ps

resolveMODALITY :: MixResolve MODALITY
resolveMODALITY ga ids m = case m of
    Term_mod t -> fmap Term_mod $ resolveMixTrm mapM_FORMULA
                  resolveM_FORMULA ga ids t
    _ -> return m

resolveM_FORMULA :: MixResolve M_FORMULA
resolveM_FORMULA ga ids cf = case cf of
   BoxOrDiamond b m f ps -> do
       nm <- resolveMODALITY ga ids m
       nf <- resolveMixFrm mapM_FORMULA resolveM_FORMULA ga ids f
       return $ BoxOrDiamond b nm nf ps

minExpForm :: Min M_FORMULA ModalSign
minExpForm s form =
    let minMod md ps = case md of
                  Simple_mod i -> minMod (Term_mod (Mixfix_token i)) ps
                  Term_mod t -> let
                    r = do
                      t2 <- oneExpTerm minExpForm s t
                      let srt = sortOfTerm t2
                          trm = Term_mod t2
                      if Map.member srt $ termModies $ extendedInfo s
                         then return trm
                         else Result [mkDiag Error
                              ("unknown term modality sort '"
                               ++ showId srt "' for term") t ]
                              $ Just trm
                    in case t of
                       Mixfix_token tm ->
                           if Map.member tm (modies $ extendedInfo s)
                              || tokStr tm == emptyS
                              then return $ Simple_mod tm
                              else Result
                                      [mkDiag Error "unknown modality" tm]
                                      $ Just $ Simple_mod tm
                       Application (Op_name (Id [tm] [] _)) [] _ ->
                           if Map.member tm (modies $ extendedInfo s)
                           then return $ Simple_mod tm
                           else r
                       _ -> r
    in case form of
        BoxOrDiamond b m f ps ->
            do nm <- minMod m ps
               f2 <- minExpFORMULA minExpForm s f
               return $ BoxOrDiamond b nm f2 ps

ana_M_SIG_ITEM :: Ana M_SIG_ITEM M_BASIC_ITEM M_SIG_ITEM M_FORMULA ModalSign
ana_M_SIG_ITEM mix mi =
    case mi of
    Rigid_op_items r al ps ->
        do ul <- mapM (ana_OP_ITEM minExpForm mix) al
           case r of
               Rigid -> mapM_ (\ aoi -> case item aoi of
                   Op_decl ops ty _ _ ->
                       mapM_ (updateExtInfo . addRigidOp (toOpType ty)) ops
                   Op_defn i par _ _ -> maybe (return ())
                       (\ ty -> updateExtInfo $ addRigidOp (toOpType ty) i)
                       $ headToType par) ul
               _ -> return ()
           return $ Rigid_op_items r ul ps
    Rigid_pred_items r al ps ->
        do ul <- mapM (ana_PRED_ITEM minExpForm mix) al
           case r of
               Rigid -> mapM_ (\ aoi -> case item aoi of
                   Pred_decl ops ty _ ->
                       mapM_ (updateExtInfo . addRigidPred (toPredType ty)) ops
                   Pred_defn i (Pred_head args _) _ _ ->
                       updateExtInfo $ addRigidPred
                                (PredType $ sortsOfArgs args) i ) ul
               _ -> return ()
           return $ Rigid_pred_items r ul ps

addRigidOp :: OpType -> Id -> ModalSign -> Result ModalSign
addRigidOp ty i m = return
       m { rigidOps = addOpTo i ty $ rigidOps m }

addRigidPred :: PredType -> Id -> ModalSign -> Result ModalSign
addRigidPred ty i m = return
       m { rigidPreds = let rps = rigidPreds m in Map.insert i
             (Set.insert ty $ Map.findWithDefault Set.empty i rps) rps }

ana_M_BASIC_ITEM
    :: Ana M_BASIC_ITEM M_BASIC_ITEM M_SIG_ITEM M_FORMULA ModalSign
ana_M_BASIC_ITEM mix bi = case bi of
        Simple_mod_decl al fs ps -> do
            mapM_ ((updateExtInfo . preAddModId) . item) al
            newFs <- mapAnM (ana_FORMULA mix) fs
            resFs <- mapAnM (return . fst) newFs
            anaFs <- mapAnM (return . snd) newFs
            mapM_ ((updateExtInfo . addModId anaFs) . item) al
            return $ Simple_mod_decl al resFs ps
        Term_mod_decl al fs ps -> do
            e <- get
            mapM_ ((updateExtInfo . preAddModSort e) . item) al
            newFs <- mapAnM (ana_FORMULA mix) fs
            resFs <- mapAnM (return . fst) newFs
            anaFs <- mapAnM (return . snd) newFs
            mapM_ ((updateExtInfo . addModSort anaFs) . item) al
            return $ Term_mod_decl al resFs ps

preAddModId :: SIMPLE_ID -> ModalSign -> Result ModalSign
preAddModId i m =
    let ms = modies m in
    if Map.member i ms then
       Result [mkDiag Hint "repeated modality" i] $ Just m
       else return m { modies = Map.insert i [] ms }

addModId :: [AnModFORM] -> SIMPLE_ID -> ModalSign -> Result ModalSign
addModId frms i m = return m
  { modies = Map.insertWith List.union i frms $ modies m }

preAddModSort :: Sign M_FORMULA ModalSign -> SORT -> ModalSign
              -> Result ModalSign
preAddModSort e i m =
    let ms = termModies m
        ds = hasSort e i
    in if Map.member i ms || not (null ds) then
       Result (mkDiag Hint "repeated term modality" i : ds) $ Just m
       else return m { termModies = Map.insert i [] ms }

addModSort :: [AnModFORM] -> SORT -> ModalSign -> Result ModalSign
addModSort frms i m = return m
  { termModies = Map.insertWith List.union i frms $ termModies m }

ana_FORMULA :: Mix M_BASIC_ITEM M_SIG_ITEM M_FORMULA ModalSign
            -> FORMULA M_FORMULA -> State (Sign M_FORMULA ModalSign)
               (FORMULA M_FORMULA, FORMULA M_FORMULA)
ana_FORMULA mix f = do
           let ps = map (mkId . (: [])) $ Set.toList $ getFormPredToks f
           pm <- gets predMap
           mapM_ (addPred (emptyAnno ()) $ PredType []) ps
           newGa <- gets globAnnos
           let Result es m = resolveFormula mapM_FORMULA
                             resolveM_FORMULA newGa (mixRules mix) f
           addDiags es
           e <- get
           phi <- case m of
               Nothing -> return (f, f)
               Just r -> do
                   n <- resultToState (minExpFORMULA minExpForm e) r
                   return (r, n)
           e2 <- get
           put e2 {predMap = pm}
           return phi

getFormPredToks :: FORMULA M_FORMULA -> Set.Set Token
getFormPredToks frm = case frm of
    Quantification _ _ f _ -> getFormPredToks f
    Conjunction fs _ -> Set.unions $ map getFormPredToks fs
    Disjunction fs _ -> Set.unions $ map getFormPredToks fs
    Implication f1 f2 _ _ ->
        Set.union (getFormPredToks f1) $ getFormPredToks f2
    Equivalence f1 f2 _ ->
        Set.union (getFormPredToks f1) $ getFormPredToks f2
    Negation f _ -> getFormPredToks f
    Mixfix_formula (Mixfix_token t) -> Set.singleton t
    Mixfix_formula t -> getTermPredToks t
    ExtFORMULA (BoxOrDiamond _ _ f _) -> getFormPredToks f
    Predication _ ts _ -> Set.unions $ map getTermPredToks ts
    Definedness t _ -> getTermPredToks t
    Existl_equation t1 t2 _ ->
        Set.union (getTermPredToks t1) $ getTermPredToks t2
    Strong_equation t1 t2 _ ->
        Set.union (getTermPredToks t1) $ getTermPredToks t2
    Membership t _ _ -> getTermPredToks t
    _ -> Set.empty

getTermPredToks :: TERM M_FORMULA -> Set.Set Token
getTermPredToks trm = case trm of
    Application _ ts _ -> Set.unions $ map getTermPredToks ts
    Sorted_term t _ _ -> getTermPredToks t
    Cast t _ _ -> getTermPredToks t
    Conditional t1 f t2 _ -> Set.union (getTermPredToks t1) $
        Set.union (getFormPredToks f) $ getTermPredToks t2
    Mixfix_term ts -> Set.unions $ map getTermPredToks ts
    Mixfix_parenthesized ts _ -> Set.unions $ map getTermPredToks ts
    Mixfix_bracketed ts _ -> Set.unions $ map getTermPredToks ts
    Mixfix_braced ts _ -> Set.unions $ map getTermPredToks ts
    _ -> Set.empty
