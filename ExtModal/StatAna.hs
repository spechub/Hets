{- |
Module      :  ./ExtModal/StatAna.hs
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

import CASL.Fold
import CASL.Sign
import CASL.MixfixParser
import CASL.StaticAna
import CASL.AS_Basic_CASL
import CASL.ShowMixfix
import CASL.Overload
import CASL.Quantification

import Common.AS_Annotation
import Common.Doc
import Common.DocUtils
import Common.GlobalAnnotations
import Common.Keywords
import Common.Lib.State
import Common.Id
import Common.Result
import Common.ExtSign
import qualified Common.Lib.MapSet as MapSet

import Data.Function
import qualified Data.HashMap.Strict as Map
import qualified Data.HashSet as Set

import Control.Monad

instance TermExtension EM_FORMULA where
  freeVarsOfExt sign frm = case frm of
    PrefixForm p f _ ->
        Set.union (freePrefixVars sign p) $ freeVars sign f
    UntilSince _ f1 f2 _ -> on Set.union (freeVars sign) f1 f2
    ModForm (ModDefn _ _ _ afs _) ->
        Set.unions $ map (freeVars sign . item)
               $ concatMap (frameForms . item) afs

freePrefixVars :: Sign EM_FORMULA e -> FormPrefix -> Set.HashSet (VAR, SORT)
freePrefixVars sign fp = case fp of
    BoxOrDiamond _ m _ _ -> freeModVars sign m
    _ -> Set.empty

freeModVars :: Sign EM_FORMULA e -> MODALITY -> Set.HashSet (VAR, SORT)
freeModVars sign md = case md of
  SimpleMod _ -> Set.empty
  TermMod t -> freeTermVars sign t
  ModOp _ m1 m2 -> on Set.union (freeModVars sign) m1 m2
  TransClos m -> freeModVars sign m
  Guard f -> freeVars sign f

basicEModalAnalysis
        :: (BASIC_SPEC EM_BASIC_ITEM EM_SIG_ITEM EM_FORMULA
           , Sign EM_FORMULA EModalSign, GlobalAnnos)
        -> Result (BASIC_SPEC EM_BASIC_ITEM EM_SIG_ITEM EM_FORMULA
                  , ExtSign (Sign EM_FORMULA EModalSign) Symbol
                  , [Named (FORMULA EM_FORMULA)])
basicEModalAnalysis s = do
  a@(_, ExtSign sig _, sens) <-
      basicAnalysis frmTypeAna basItemStatAna sigItemStatAna mixfixAna s
  checkConstr sig sens
  return a

checkConstr :: Sign EM_FORMULA EModalSign -> [Named (FORMULA EM_FORMULA)]
  -> Result ()
checkConstr sig sens =
  let cs = interOpMapSet
        (Set.foldr (uncurry addOpTo) MapSet.empty $ getConstructors sens)
        $ flexOps $ extendedInfo sig
  in unless (MapSet.null cs) $ fail $ "constructors must not be flexible:\n"
         ++ show (printSetMap empty empty $ MapSet.toMap cs)

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
  checkFrame (FrameForm vs fs r) = do
    nfs <- mapAnM (minExpFORMULA frmTypeAna sign . mkForall vs) fs
    return $ FrameForm [] nfs r
  checkPrefix pf = case pf of
       BoxOrDiamond choice md leq_geq number -> do
         new_md <- checkMod md
         let new_pf = BoxOrDiamond choice new_md leq_geq number
         if number >= 0
           then return new_pf
           else Result [mkDiag Error "negative number grading" number]
                  $ Just new_pf
       Hybrid _ nm ->
         if Set.member (nomPId nm) (nominals $ extendedInfo sign)
           then return pf
           else Result [mkDiag Error "unknown nominal" nm]
                    $ Just pf
       _ -> return pf
  in case form of
       PrefixForm pf f pos -> do
         new_pf <- checkPrefix pf
         new_f <- minExpFORMULA frmTypeAna sign f
         return $ PrefixForm new_pf new_f pos
       UntilSince choice f1 f2 pos -> do
         new_f1 <- minExpFORMULA frmTypeAna sign f1
         new_f2 <- minExpFORMULA frmTypeAna sign f2
         return $ UntilSince choice new_f1 new_f2 pos
       ModForm (ModDefn is_time isTerm anno_list forms pos) -> do
         new_forms <- mapAnM checkFrame forms
         return $ ModForm $ ModDefn is_time isTerm anno_list new_forms pos

anaFrameForm :: Mix b s EM_FORMULA EModalSign -> FrameForm
  -> State (Sign EM_FORMULA EModalSign) (FrameForm, FrameForm)
anaFrameForm mix ff@(FrameForm vs fs r) = if null fs then do
    mapM_ addVars vs
    return (ff, ff)
  else do
    (resFs, fufs) <- anaLocalVarForms (anaFORMULA mix) vs fs r
    return (FrameForm vs resFs r, FrameForm [] fufs r)

clearVarMap :: State (Sign f e) ()
clearVarMap = do
  e <- get
  put e { varMap = Map.empty }

modItemStatAna
  :: Ana ModDefn EM_BASIC_ITEM EM_SIG_ITEM EM_FORMULA EModalSign
modItemStatAna mix (ModDefn is_time isTerm anno_list forms pos) = do
    mapM_ ( (updateExtInfo . addMod) . item ) anno_list
    clearVarMap -- forget vars beyond this point
    new_forms <- mapAnM (anaFrameForm mix) forms
    clearVarMap -- forget vars after this point
    let res_forms = map (fmap fst) new_forms
        ana_forms = filter (not . null . frameForms . item)
          $ map (fmap snd) new_forms
    unless (null ana_forms)
      $ addSentences $ map (\ af ->
           (makeNamed (getRLabel af) $ ExtFORMULA $ ModForm
             $ ModDefn is_time isTerm anno_list [emptyAnno $ item af] pos)
           { isAxiom = notImplied af })
           ana_forms
    when is_time $ mapM_ (updateExtInfo . addTimeMod . item ) anno_list
    when isTerm $ do
      sig <- get
      mapM_ ( (updateExtInfo . addTermMod sig) . item ) anno_list
    return $ ModDefn is_time isTerm anno_list res_forms pos

basItemStatAna
  :: Ana EM_BASIC_ITEM EM_BASIC_ITEM EM_SIG_ITEM EM_FORMULA EModalSign
basItemStatAna mix basic_item = case basic_item of
  ModItem md -> fmap ModItem $ modItemStatAna mix md
  Nominal_decl anno_list pos -> do
    mapM_ (updateExtInfo . addNom . nomPId . item) anno_list
    mapM_ (addPred (emptyAnno ()) nomPType . nomPId . item) anno_list
    return $ Nominal_decl anno_list pos

addTermMod :: Sign f e -> Id -> EModalSign -> Result EModalSign
addTermMod fullSign tmi sgn = let
  tm = termMods sgn
  srts = sortSet fullSign
  in if Set.member tmi srts then
     if Set.member tmi tm
     then Result [mkDiag Hint "repeated term modality" tmi] $ Just sgn
     else let sps = Set.intersection tm $ supersortsOf tmi fullSign in
       if Set.null sps
       then return sgn { termMods = Set.insert tmi tm }
       else Result [mkDiag Warning
         ("term modality known for supersorts " ++ showDoc sps "")
         tmi] $ Just sgn
  else Result [mkDiag Error "unknown sort in term modality" tmi] $ Just sgn

addTimeMod :: Id -> EModalSign -> Result EModalSign
addTimeMod tmi sgn = let tm = timeMods sgn in
  if Set.member tmi tm
  then Result [mkDiag Hint "repeated time modality" tmi] $ Just sgn
  else if Set.size tm >= 1
       then Result [mkDiag Hint "more than one time modality" tmi] $ Just sgn
       else return sgn { timeMods = Set.insert tmi tm }

addMod :: Id -> EModalSign -> Result EModalSign
addMod mi sgn =
        let m = modalities sgn in
        if Set.member mi m then
                Result [mkDiag Hint "repeated modality" mi] $ Just sgn
                else return sgn { modalities = Set.insert mi m }

addNom :: Id -> EModalSign -> Result EModalSign
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
    unless rig $ mapM_
        (\ nlitem -> case item nlitem of
          Op_decl ops typ _ _ ->
              mapM_ (updateExtInfo . addFlexOp (toOpType typ)) ops
          Op_defn op hd _ _ -> maybe (return ())
              (\ ty -> updateExtInfo $ addFlexOp (toOpType ty) op)
              $ headToType hd
        ) new_list
    return $ Rigid_op_items rig new_list pos
  Rigid_pred_items rig ann_list pos -> do
    new_list <- mapM (ana_PRED_ITEM frmTypeAna mix) ann_list
    unless rig $ mapM_ ( \ nlitem -> case item nlitem of
          Pred_decl preds typ _ ->
              mapM_ (updateExtInfo . addFlexPred (toPredType typ) ) preds
          Pred_defn prd (Pred_head args _ ) _ _ ->
              updateExtInfo $ addFlexPred (PredType $ sortsOfArgs args) prd
                     ) new_list
    return $ Rigid_pred_items rig new_list pos

addFlexOp :: OpType -> Id -> EModalSign -> Result EModalSign
addFlexOp typ i sgn = return
        sgn { flexOps = addOpTo i typ $ flexOps sgn }

addFlexPred :: PredType -> Id -> EModalSign -> Result EModalSign
addFlexPred typ i sgn = return
        sgn { flexPreds = MapSet.insert i typ $ flexPreds sgn }

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
parenExtForm = mapExtForm (mapFormula parenExtForm)

mapExtMod :: (FORMULA EM_FORMULA -> FORMULA EM_FORMULA)
  -> MODALITY -> MODALITY
mapExtMod f m = case m of
    ModOp o md1 md2 -> on (ModOp o) (mapExtMod f) md1 md2
    TransClos md -> TransClos $ mapExtMod f md
    Guard frm -> Guard $ f frm
    TermMod t -> let Mixfix_formula n = f (Mixfix_formula t) in TermMod n
    _ -> m

mapExtPrefix :: (FORMULA EM_FORMULA -> FORMULA EM_FORMULA)
  -> FormPrefix -> FormPrefix
mapExtPrefix f pf = case pf of
    BoxOrDiamond choice md leq_geq nr ->
        BoxOrDiamond choice (mapExtMod f md) leq_geq nr
    _ -> pf

mapExtForm :: (FORMULA EM_FORMULA -> FORMULA EM_FORMULA)
  -> EM_FORMULA -> EM_FORMULA
mapExtForm f ef = case ef of
    PrefixForm p frm pos ->
        PrefixForm (mapExtPrefix f p) (f frm) pos
    UntilSince choice f1 f2 pos ->
        UntilSince choice (f f1) (f f2) pos
    ModForm (ModDefn ti te is fs pos) -> ModForm $ ModDefn
        ti te is (map (fmap $ mapExtFrameForm f) fs) pos

mapExtFrameForm :: (FORMULA EM_FORMULA -> FORMULA EM_FORMULA)
  -> FrameForm -> FrameForm
mapExtFrameForm f (FrameForm vs fs r) = FrameForm vs (map (fmap f) fs) r

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

resolvePrefix :: MixResolve FormPrefix
resolvePrefix ga ids pf = case pf of
    BoxOrDiamond choice ms leq_geq nr -> do
      nms <- resolveMod ga ids ms
      return $ BoxOrDiamond choice nms leq_geq nr
    _ -> return pf

resolveExtForm :: MixResolve EM_FORMULA
resolveExtForm ga ids f =
  let recResolve = resolveMixFrm parenExtForm resolveExtForm ga ids
  in case f of
    PrefixForm p frm pos -> do
      np <- resolvePrefix ga ids p
      new_frm <- recResolve frm
      return $ PrefixForm np new_frm pos
    UntilSince choice f1 f2 pos -> do
      new_f1 <- recResolve f1
      new_f2 <- recResolve f2
      return $ UntilSince choice new_f1 new_f2 pos
    ModForm (ModDefn ti te is fs pos) -> do
      nfs <- mapAnM (resolveFrameForm ga ids) fs
      return $ ModForm $ ModDefn ti te is nfs pos

resolveFrameForm :: MixResolve FrameForm
resolveFrameForm ga ids (FrameForm vs fs r) = do
    let ts = varDeclTokens vs
    nfs <- mapAnM (resolveMixFrm parenExtForm
                   (extendMixResolve ts resolveExtForm) ga
                  $ extendRules ts ids) fs
    return $ FrameForm vs nfs r

anaFORMULA :: Mix b s EM_FORMULA EModalSign -> Sign EM_FORMULA EModalSign
  -> FORMULA EM_FORMULA -> Result (FORMULA EM_FORMULA, FORMULA EM_FORMULA)
anaFORMULA mix sig f = do
    let mix2 = extendMix (Set.fromList $ Map.keys $ varMap sig) mix
    -- the unknown predicates are not needed for mixfix resolution
    r <- resolveFormula parenExtForm
                  resolveExtForm (globAnnos sig) (mixRules mix2) f
    let q = Set.foldr
          (\ t -> QuantPred (simpleIdToId t) (Pred_type [] $ tokPos t))
          r $ getFormPredToks f
    n <- minExpFORMULA frmTypeAna sig q
    return (r, n)

getEFormPredToks :: EM_FORMULA -> Set.HashSet Token
getEFormPredToks ef = case ef of
    PrefixForm _ f _ -> getFormPredToks f
    UntilSince _ f1 f2 _ -> on Set.union getFormPredToks f1 f2
    ModForm _ -> Set.empty

getFormPredToks :: FORMULA EM_FORMULA -> Set.HashSet Token
getFormPredToks = foldFormula
  (constRecord getEFormPredToks Set.unions Set.empty)
    { foldMixfix_formula = \ f ts -> case f of
         Mixfix_formula (Mixfix_token t) -> Set.singleton t
         _ -> ts
    , foldQuantPred = \ _ i _ ts -> if isSimpleId i then
        Set.delete (idToSimpleId i) ts else ts
    }
