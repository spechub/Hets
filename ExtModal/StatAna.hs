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
import Common.DocUtils
import Common.GlobalAnnotations
import Common.Keywords
import Common.Lib.State
import Common.Id
import Common.Result
import Common.ExtSign
import qualified Common.Lib.MapSet as MapSet

import qualified Data.Set as Set

import Control.Monad

instance TermExtension EM_FORMULA where
  freeVarsOfExt sign frm = case frm of
    BoxOrDiamond _ _ _ _ f _ -> freeVars sign f
    Hybrid _ _ f _ -> freeVars sign f
    UntilSince _ f1 f2 _ -> Set.union (freeVars sign f1) $ freeVars sign f2
    PathQuantification _ f _ -> freeVars sign f
    StateQuantification _ _ f _ -> freeVars sign f
    NextY _ f _ -> freeVars sign f
    FixedPoint _ _ f _ -> freeVars sign f
    ModForm (ModDefn _ _ _ afs _) ->
        Set.unions $ map (freeVars sign . item) afs

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
    SimpleMod s_id ->
      if tokStr s_id == emptyS
         || Set.member (simpleIdToId s_id) (modalities $ extendedInfo sign)
      then return $ SimpleMod s_id
      else Result [mkDiag Error "unknown modality" s_id]
               $ Just $ SimpleMod s_id
    ModOp o md1 md2 -> do
      new_md1 <- checkMod md1
      new_md2 <- checkMod md2
      return $ ModOp o new_md1 new_md2
    TransClos md -> fmap TransClos $ checkMod md
    Guard frm -> fmap Guard $ minExpFORMULA frmTypeAna sign frm
    TermMod t -> let
                    ms = modalities $ extendedInfo sign
                    r = do
                      t2 <- oneExpTerm frmTypeAna sign t
                      let srt = sortOfTerm t2
                          trm = TermMod t2
                          supers = supersortsOf srt sign
                      if Set.null $ Set.intersection (Set.insert srt supers) ms
                         then Result [mkDiag Error
                              ("unknown term modality sort '"
                               ++ showId srt "' for term") t ]
                              $ Just trm
                         else return trm
                    in case t of
                       Mixfix_token tm ->
                           if Set.member (simpleIdToId tm) ms
                              || tokStr tm == emptyS
                              then return $ SimpleMod tm
                              else Result
                                      [mkDiag Error "unknown modality" tm]
                                      $ Just $ SimpleMod tm
                       Application (Op_name (Id [tm] [] _)) [] _ ->
                           if Set.member (simpleIdToId tm) ms
                           then return $ SimpleMod tm
                           else r
                       _ -> r
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
         if Set.member nm (nominals $ extendedInfo sign)
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
       ModForm (ModDefn is_time isTerm anno_list forms pos) -> do
         new_forms <- mapAnM (minExpFORMULA frmTypeAna sign) forms
         return $ ModForm $ ModDefn is_time isTerm anno_list new_forms pos

modItemStatAna
  :: Ana ModDefn EM_BASIC_ITEM EM_SIG_ITEM EM_FORMULA EModalSign
modItemStatAna mix (ModDefn is_time isTerm anno_list forms pos) = do
    mapM_ ( (updateExtInfo . addMod) . item ) anno_list
    new_forms <- mapAnM (ana_FORMULA mix) forms
    let res_forms = map (fmap fst) new_forms
        ana_forms = map (fmap snd) new_forms
    unless (null forms)
      $ addSentences [makeNamed "" $ ExtFORMULA $ ModForm
        $ ModDefn is_time isTerm anno_list ana_forms pos]
    when is_time $ mapM_ ( (updateExtInfo . addTimeMod ) . item ) anno_list
    when isTerm $ do
      sig <- get
      mapM_ ( (updateExtInfo . addTermMod sig) . item ) anno_list
    return $ ModDefn is_time isTerm anno_list res_forms pos

basItemStatAna
  :: Ana EM_BASIC_ITEM EM_BASIC_ITEM EM_SIG_ITEM EM_FORMULA EModalSign
basItemStatAna mix basic_item = case basic_item of
  ModItem md -> fmap ModItem $ modItemStatAna mix md
  Nominal_decl anno_list pos -> do
    mapM_ (updateExtInfo . addNom . item) anno_list
    mapM_ (addPred (emptyAnno ()) (PredType []) . mkId . (: []) . item)
       anno_list
    return $ Nominal_decl anno_list pos

addTermMod :: Sign f e -> Id -> EModalSign -> Result EModalSign
addTermMod fullSign tmi sgn = let
  tm = termMods sgn
  srts = sortSet fullSign
  in if Set.member tmi srts then
     if Set.member tmi tm
     then Result [mkDiag Hint "repeated term modality" tmi] $ Just sgn
     else let sps = Set.difference tm $ supersortsOf tmi fullSign in
       if Set.null sps
       then return sgn { termMods = Set.insert tmi tm }
       else Result [mkDiag Warning
         ("term modality known for supersorts " ++ showDoc sps "")
         tmi] $ Just sgn
  else Result [mkDiag Error "unknown sort in term modality" tmi] $ Just sgn

addTimeMod :: Id -> EModalSign -> Result EModalSign
addTimeMod tmi sgn = let tm = time_modalities sgn in
  if Set.member tmi tm
  then Result [mkDiag Hint "repeated time modality" tmi] $ Just sgn
  else if Set.size tm >= 1
       then Result [mkDiag Hint "more than one time modality" tmi] $ Just sgn
       else return sgn { time_modalities = Set.insert tmi tm }

addMod :: Id -> EModalSign -> Result EModalSign
addMod mi sgn =
        let m = modalities sgn in
        if Set.member mi m then
                Result [mkDiag Hint "repeated modality" mi] $ Just sgn
                else return sgn { modalities = Set.insert mi m }

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
    when rig $ mapM_
        (\ nlitem -> case item nlitem of
          Op_decl ops typ _ _ ->
              mapM_ (updateExtInfo . addRigidOp (toOpType typ)) ops
          Op_defn op hd _ _ -> maybe (return ())
              (\ ty -> updateExtInfo $ addRigidOp (toOpType ty) op)
              $ headToType hd
        ) new_list
    return $ Rigid_op_items rig new_list pos
  Rigid_pred_items rig ann_list pos -> do
    new_list <- mapM (ana_PRED_ITEM frmTypeAna mix) ann_list
    when rig $ mapM_ ( \ nlitem -> case item nlitem of
          Pred_decl preds typ _ ->
              mapM_ (updateExtInfo . addRigidPred (toPredType typ) ) preds
          Pred_defn prd (Pred_head args _ ) _ _ ->
              updateExtInfo $ addRigidPred (PredType $ sortsOfArgs args) prd
                     ) new_list
    return $ Rigid_pred_items rig new_list pos

addRigidOp :: OpType -> Id -> EModalSign -> Result EModalSign
addRigidOp typ i sgn = return
        sgn { rigidOps = addOpTo i typ $ rigidOps sgn }

addRigidPred :: PredType -> Id -> EModalSign -> Result EModalSign
addRigidPred typ i sgn = return
        sgn { rigidPreds = MapSet.insert i typ $ rigidPreds sgn }

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

parenMod :: MODALITY -> MODALITY
parenMod m = case m of
    ModOp o md1 md2 -> ModOp o (parenMod md1) $ parenMod md2
    TransClos md -> TransClos $ parenMod md
    Guard frm -> Guard $ mapFormula parenExtForm frm
    TermMod t -> TermMod $ mapTerm parenExtForm t
    _ -> m

parenExtForm :: EM_FORMULA -> EM_FORMULA
parenExtForm f = case f of
    BoxOrDiamond choice md leq_geq nr frm pos ->
        BoxOrDiamond choice (parenMod md) leq_geq nr
            (mapFormula parenExtForm frm) pos
    Hybrid choice nom frm pos ->
        Hybrid choice nom (mapFormula parenExtForm frm) pos
    UntilSince choice f1 f2 pos ->
        UntilSince choice (mapFormula parenExtForm f1)
                       (mapFormula parenExtForm f2) pos
    PathQuantification choice frm pos ->
        PathQuantification choice (mapFormula parenExtForm frm) pos
    StateQuantification t_dir choice frm pos ->
        StateQuantification t_dir choice (mapFormula parenExtForm frm) pos
    NextY choice frm pos ->
        NextY choice (mapFormula parenExtForm frm) pos
    FixedPoint choice fpvar frm pos ->
        FixedPoint choice fpvar (mapFormula parenExtForm frm) pos
    ModForm (ModDefn ti te is fs pos) -> ModForm $ ModDefn
        ti te is (map (fmap $ mapFormula parenExtForm) fs) pos

resolveMod :: MixResolve MODALITY
resolveMod ga ids m = case m of
    ModOp o md1 md2 -> do
      new_md1 <- resolveMod ga ids md1
      new_md2 <- resolveMod ga ids md2
      return $ ModOp o new_md1 new_md2
    TransClos md -> fmap TransClos $ resolveMod ga ids md
    Guard frm -> fmap Guard
      $ resolveMixFrm parenExtForm resolveExtForm ga ids frm
    TermMod t -> fmap TermMod
      $ resolveMixTrm parenExtForm resolveExtForm ga ids t
    _ -> return m

resolveExtForm :: MixResolve EM_FORMULA
resolveExtForm ga ids f = case f of
    BoxOrDiamond choice ms leq_geq nr frm pos -> do
      nms <- resolveMod ga ids ms
      new_frm <- resolveMixFrm parenExtForm resolveExtForm ga ids frm
      return $ BoxOrDiamond choice nms leq_geq nr new_frm pos
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
    ModForm (ModDefn ti te is fs pos) -> do
      nfs <- mapAnM (resolveMixFrm parenExtForm resolveExtForm ga ids) fs
      return $ ModForm $ ModDefn ti te is nfs pos

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
