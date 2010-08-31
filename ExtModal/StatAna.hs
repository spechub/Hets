{- |
Module      :  $Header$
Copyright   :  DFKI GmbH 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  codruta.liliana@gmail.com
Stability   :  experimental
Portability :  portable

static analysis of modal logic parts
-}

module ExtModal.StatAna where

import ExtModal.AS_ExtModal
import ExtModal.Print_AS ()
import ExtModal.ExtModalSign

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
import qualified Data.List as List

instance FreeVars EM_FORMULA where
        freeVarsOfExt sign ( BoxOrDiamond _ _ _ _ f _ ) = freeVars sign f
        freeVarsOfExt sign ( Hybrid _ _ f _ ) = freeVars sign f
        freeVarsOfExt sign ( UntilSince _ f1 f2 _ ) = Set.union
          (freeVars sign f1) (freeVars sign f2)
        freeVarsOfExt sign ( PathQuantification _ f _ ) = freeVars sign f
        freeVarsOfExt sign ( StateQuantification _ _ f _ ) = freeVars sign f
        freeVarsOfExt sign ( NextY _ f _ ) = freeVars sign f
        freeVarsOfExt sign ( FixedPoint _ _ f _ ) = freeVars sign f

basicEModalAnalysis
        :: (BASIC_SPEC EM_BASIC_ITEM EM_SIG_ITEM EM_FORMULA
           , Sign EM_FORMULA EModalSign, GlobalAnnos)
        -> Result (BASIC_SPEC EM_BASIC_ITEM EM_SIG_ITEM EM_FORMULA
                  , ExtSign (Sign EM_FORMULA EModalSign) Symbol
                  , [Named (FORMULA EM_FORMULA)])
basicEModalAnalysis =
  basicAnalysis frmTypeAna basItemStatAna sigItemStatAna mixfixAna


frmTypeAna :: Min EM_FORMULA EModalSign
frmTypeAna sign form = let
  checkMod term_mod = case term_mod of
    Simple_modality s_id ->
      if tokStr s_id == emptyS
         || Map.member s_id (modalities $ extendedInfo sign)
      then return $ Simple_modality s_id
      else Result [mkDiag Error "unknown modality" s_id]
               $ Just $ Simple_modality s_id
    Composition md1 md2 -> do
      new_md1 <- checkMod md1
      new_md2 <- checkMod md2
      return $ Composition new_md1 new_md2
    Union md1 md2 -> do
      new_md1 <- checkMod md1
      new_md2 <- checkMod md2
      return $ Union new_md1 new_md2
    TransitiveClosure md -> fmap TransitiveClosure $ checkMod md
    Guard frm -> fmap Guard $ minExpFORMULA frmTypeAna sign frm
  in case form of
       BoxOrDiamond choice md leq_geq number f pos -> do
         new_md <- checkMod md
         new_f <- minExpFORMULA frmTypeAna sign f
         if number >= 0
           then return $ BoxOrDiamond choice new_md leq_geq number new_f pos
           else Result [mkDiag Error "negative number grading" number]
                  $ Just $ BoxOrDiamond choice new_md leq_geq number new_f pos
       Hybrid choice nm f pos -> do
         new_f <- minExpFORMULA frmTypeAna sign f
         let id_of_nom ( Nominal sid ) = sid
         if Set.member (id_of_nom nm) (nominals $ extendedInfo sign)
           then return $ Hybrid choice nm new_f pos
           else Result [mkDiag Error "unknown nominal" nm]
                    $ Just $ Hybrid choice nm new_f pos
       UntilSince choice f1 f2 pos -> do
         new_f1 <- minExpFORMULA frmTypeAna sign f1
         new_f2 <- minExpFORMULA frmTypeAna sign f2
         return $ UntilSince choice new_f1 new_f2 pos
       PathQuantification choice f pos -> do
         new_f <- minExpFORMULA frmTypeAna sign f
         return $ PathQuantification choice new_f pos
       StateQuantification t_dir choice f pos -> do
         new_f <- minExpFORMULA frmTypeAna sign f
         return $ StateQuantification t_dir choice new_f pos
       NextY choice f pos -> do
         new_f <- minExpFORMULA frmTypeAna sign f
         return $ NextY choice new_f pos
       FixedPoint choice fpvar f pos -> do
         new_f <- minExpFORMULA frmTypeAna sign f
         return $ FixedPoint choice fpvar new_f pos


basItemStatAna
  :: Ana EM_BASIC_ITEM EM_BASIC_ITEM EM_SIG_ITEM EM_FORMULA EModalSign
basItemStatAna mix basic_item = case basic_item of
  Simple_mod_decl is_time anno_list forms pos -> do
    mapM_ ( (updateExtInfo . preAddMod) . item ) anno_list
    new_forms <- mapAnM (ana_FORMULA mix) forms
    res_forms <- mapAnM (return . fst) new_forms
    ana_forms <- mapAnM (return . snd) new_forms
    mapM_ ( (updateExtInfo . addMod ana_forms) . item ) anno_list
    if not is_time
      then return $ Simple_mod_decl is_time anno_list res_forms pos
      else do
        mapM_ ( (updateExtInfo . addTimeMod ) . item ) anno_list
        return $ Simple_mod_decl is_time anno_list res_forms pos
  Nominal_decl anno_list pos -> do
    mapM_ ( (updateExtInfo . addNom) . item ) anno_list
    return $ Nominal_decl anno_list pos

addTimeMod :: SIMPLE_ID -> EModalSign -> Result EModalSign
addTimeMod tmi sgn = let tm = time_modalities sgn in
  if Set.member tmi tm
  then Result [mkDiag Hint "repeated time modality" tmi] $ Just sgn
  else if Set.size tm >= 1
       then Result [mkDiag Hint "more than one time modality" tmi] $ Just sgn
       else return sgn { time_modalities = Set.insert tmi tm }

preAddMod :: SIMPLE_ID -> EModalSign -> Result EModalSign
preAddMod mi sgn =
        let m = modalities sgn in
        if Map.member mi m then
                Result [mkDiag Hint "repeated modality" mi] $ Just sgn
                else return sgn { modalities = Map.insert mi [] m }

addMod :: [AnEModForm] -> SIMPLE_ID -> EModalSign -> Result EModalSign
addMod forms mi sgn = return sgn
  { modalities = Map.insertWith List.union mi forms $ modalities sgn }

addNom :: SIMPLE_ID -> EModalSign -> Result EModalSign
addNom ni sgn =
        let n = nominals sgn in
        if Set.member ni n then
                Result [mkDiag Hint "repeated nominal" ni] $ Just sgn
                else return sgn { nominals = Set.insert ni n }

sigItemStatAna
  :: Ana EM_SIG_ITEM EM_BASIC_ITEM EM_SIG_ITEM EM_FORMULA EModalSign
sigItemStatAna mix sig_item = case sig_item of
  Rigid_op_items rig ann_list pos -> do
    new_list <- mapM (ana_OP_ITEM frmTypeAna mix) ann_list
    case rig of
      Rigid -> mapM_ ( \ nlitem -> case item nlitem of
          Op_decl ops typ _ _ ->
              mapM_ (updateExtInfo . addRigidOp (toOpType typ)) ops
          Op_defn op hd _ _ ->
              updateExtInfo $ addRigidOp (toOpType $ headToType hd) op
                     ) new_list
      _ -> return ()
    return $ Rigid_op_items rig new_list pos
  Rigid_pred_items rig ann_list pos -> do
    new_list <- mapM (ana_PRED_ITEM frmTypeAna mix) ann_list
    case rig of
      Rigid -> mapM_ ( \ nlitem -> case item nlitem of
          Pred_decl preds typ _ ->
              mapM_ (updateExtInfo . addRigidPred (toPredType typ) ) preds
          Pred_defn prd (Pred_head args _ ) _ _ ->
              updateExtInfo $ addRigidPred (PredType $ sortsOfArgs args) prd
                     ) new_list
      _ -> return ()
    return $ Rigid_pred_items rig new_list pos

addRigidOp :: OpType -> Id -> EModalSign -> Result EModalSign
addRigidOp typ i sgn = return
        sgn { rigidOps = addOpTo i typ $ rigidOps sgn }

addRigidPred :: PredType -> Id -> EModalSign -> Result EModalSign
addRigidPred typ i sgn = return
        sgn { rigidPreds = let old_rpreds = rigidPreds sgn in
                Map.insert i
                (Set.insert typ $ Map.findWithDefault Set.empty i old_rpreds)
                old_rpreds
                }

mixfixAna :: Mix EM_BASIC_ITEM EM_SIG_ITEM EM_FORMULA EModalSign
mixfixAna = emptyMix
        { getSigIds = extraSigItems
        , putParen = parenExtForm
        , mixResolve = resolveExtForm
        }

extraSigItems :: EM_SIG_ITEM -> IdSets
extraSigItems s = let e = Set.empty in case s of
        Rigid_op_items _ annoted_list _ ->
            (unite2 $ map (ids_OP_ITEM . item) annoted_list, e)
        Rigid_pred_items _ annoted_list _ ->
            ((e, e), Set.unions $ map (ids_PRED_ITEM . item) annoted_list)

parenExtForm :: EM_FORMULA -> EM_FORMULA
parenExtForm (BoxOrDiamond choice md leq_geq nr frm pos) =
        BoxOrDiamond choice md leq_geq nr (mapFormula parenExtForm frm) pos
parenExtForm (Hybrid choice nom frm pos) =
        Hybrid choice nom (mapFormula parenExtForm frm) pos
parenExtForm (UntilSince choice f1 f2 pos) =
        UntilSince choice (mapFormula parenExtForm f1)
                       (mapFormula parenExtForm f2) pos
parenExtForm (PathQuantification choice frm pos) =
        PathQuantification choice (mapFormula parenExtForm frm) pos
parenExtForm (StateQuantification t_dir choice frm pos) =
        StateQuantification t_dir choice (mapFormula parenExtForm frm) pos
parenExtForm (NextY choice frm pos) =
        NextY choice (mapFormula parenExtForm frm) pos
parenExtForm (FixedPoint choice fpvar frm pos) =
        FixedPoint choice fpvar (mapFormula parenExtForm frm) pos

resolveExtForm :: MixResolve EM_FORMULA
resolveExtForm ga ids f = case f of
        BoxOrDiamond choice ms leq_geq nr frm pos -> do
                new_frm <- resolveMixFrm parenExtForm resolveExtForm ga ids frm
                return $ BoxOrDiamond choice ms leq_geq nr new_frm pos
        Hybrid choice nom frm pos -> do
                new_frm <- resolveMixFrm parenExtForm resolveExtForm ga ids frm
                return $ Hybrid choice nom new_frm pos
        UntilSince choice f1 f2 pos -> do
                new_f1 <- resolveMixFrm parenExtForm resolveExtForm ga ids f1
                new_f2 <- resolveMixFrm parenExtForm resolveExtForm ga ids f2
                return $ UntilSince choice new_f1 new_f2 pos
        PathQuantification choice frm pos -> do
                new_frm <- resolveMixFrm parenExtForm resolveExtForm ga ids frm
                return $ PathQuantification choice new_frm pos
        StateQuantification t_dir choice frm pos -> do
                new_frm <- resolveMixFrm parenExtForm resolveExtForm ga ids frm
                return $ StateQuantification t_dir choice new_frm pos
        NextY choice frm pos -> do
                new_frm <- resolveMixFrm parenExtForm resolveExtForm ga ids frm
                return $ NextY choice new_frm pos
        FixedPoint choice fpvar frm pos -> do
                new_frm <- resolveMixFrm parenExtForm resolveExtForm ga ids frm
                return $ FixedPoint choice fpvar new_frm pos

ana_FORMULA :: Mix EM_BASIC_ITEM EM_SIG_ITEM EM_FORMULA EModalSign
            -> FORMULA EM_FORMULA -> State (Sign EM_FORMULA EModalSign)
               (FORMULA EM_FORMULA, FORMULA EM_FORMULA)
ana_FORMULA mix f = do
           let ps = map (mkId . (: [])) $ Set.toList $ getFormPredToks f
           pm <- gets predMap
           mapM_ (addPred (emptyAnno ()) $ PredType []) ps
           newGa <- gets globAnnos
           let Result es m = resolveFormula parenExtForm
                             resolveExtForm newGa (mixRules mix) f
           addDiags es
           e <- get
           phi <- case m of
               Nothing -> return (f, f)
               Just r -> do
                   n <- resultToState (minExpFORMULA frmTypeAna e) r
                   return (r, n)
           e2 <- get
           put e2 {predMap = pm}
           return phi

getFormPredToks :: FORMULA EM_FORMULA -> Set.Set Token
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
    ExtFORMULA (BoxOrDiamond _ _ _ _ f _) -> getFormPredToks f
    ExtFORMULA (Hybrid _ _ f _ ) -> getFormPredToks f
    ExtFORMULA (UntilSince _ f1 f2 _ ) ->
        Set.union (getFormPredToks f1) (getFormPredToks f2)
    ExtFORMULA (NextY _ f _ ) -> getFormPredToks f
    ExtFORMULA (PathQuantification _ f _ ) -> getFormPredToks f
    ExtFORMULA (StateQuantification _ _ f _ ) -> getFormPredToks f
    ExtFORMULA (FixedPoint _ _ f _ ) -> getFormPredToks f
    Predication _ ts _ -> Set.unions $ map getTermPredToks ts
    Definedness t _ -> getTermPredToks t
    Existl_equation t1 t2 _ ->
        Set.union (getTermPredToks t1) $ getTermPredToks t2
    Strong_equation t1 t2 _ ->
        Set.union (getTermPredToks t1) $ getTermPredToks t2
    Membership t _ _ -> getTermPredToks t
    _ -> Set.empty

getTermPredToks :: TERM EM_FORMULA -> Set.Set Token
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
