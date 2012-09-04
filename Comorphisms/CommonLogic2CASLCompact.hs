{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  Comorphism from CommonLogic to CASL
Copyright   :  (c) Eugen Kuksa, Uni Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  eugenk@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (via Logic.Logic)

Translating comorphism from Common Logic
(compact, that is without sequence markers) to CASL

-}

module Comorphisms.CommonLogic2CASLCompact
   (
     CommonLogic2CASLCompact (..)
   )
   where

import Logic.Logic as Logic
import Logic.Comorphism

import Common.ProofTree
import Common.Result
import Common.AS_Annotation as AS_Anno
import Common.Lib.MapSet (MapSet)
import Common.DocUtils (pretty)
import qualified Common.Lib.MapSet as MapSet
import qualified Common.Lib.Rel as Rel
import qualified Common.Id as Id

import Data.Function (on)
import Data.List (partition, intersect)
import qualified Data.Set as Set
import qualified Data.Map as Map

-- Common Logic
import qualified CommonLogic.Logic_CommonLogic as ClLogic
import qualified CommonLogic.AS_CommonLogic as Cl
import qualified CommonLogic.Sign as ClSign
import qualified CommonLogic.Symbol as ClSymbol
import qualified CommonLogic.Morphism as ClMor
import qualified CommonLogic.Sublogic as ClSl

import Comorphisms.CommonLogicModuleElimination (eliminateModules)

-- CASL
import qualified CASL.Logic_CASL as CLogic
import qualified CASL.AS_Basic_CASL as CBasic
import qualified CASL.Sublogic as CSL
import qualified CASL.Sign as CSign
import qualified CASL.Morphism as CMor

data CommonLogic2CASLCompact = CommonLogic2CASLCompact deriving Show

instance Language CommonLogic2CASLCompact where
  language_name CommonLogic2CASLCompact = "CommonLogic2CASLCompact"

instance Comorphism
    CommonLogic2CASLCompact -- comorphism
    ClLogic.CommonLogic     -- lid domain
    ClSl.CommonLogicSL      -- sublogics codomain
    Cl.BASIC_SPEC           -- Basic spec domain
    Cl.TEXT_META            -- sentence domain
    Cl.SYMB_ITEMS           -- symbol items domain
    Cl.SYMB_MAP_ITEMS       -- symbol map items domain
    ClSign.Sign             -- signature domain
    ClMor.Morphism          -- morphism domain
    ClSymbol.Symbol         -- symbol domain
    ClSymbol.Symbol         -- rawsymbol domain
    ProofTree               -- proof tree codomain
    CLogic.CASL             -- lid codomain
    CSL.CASL_Sublogics      -- sublogics codomain
    CLogic.CASLBasicSpec    -- Basic spec codomain
    CBasic.CASLFORMULA      -- sentence codomain
    CBasic.SYMB_ITEMS       -- symbol items codomain
    CBasic.SYMB_MAP_ITEMS   -- symbol map items codomain
    CSign.CASLSign          -- signature codomain
    CMor.CASLMor            -- morphism codomain
    CSign.Symbol            -- symbol codomain
    CMor.RawSymbol          -- rawsymbol codomain
    ProofTree               -- proof tree domain
    where
      sourceLogic CommonLogic2CASLCompact = ClLogic.CommonLogic
      sourceSublogic CommonLogic2CASLCompact = ClSl.compactsl
      targetLogic CommonLogic2CASLCompact = CLogic.CASL
      mapSublogic CommonLogic2CASLCompact = Just . mapSub
      map_theory CommonLogic2CASLCompact = mapTheory
      map_morphism CommonLogic2CASLCompact = mapMor
      map_sentence CommonLogic2CASLCompact = mapSentence
      has_model_expansion CommonLogic2CASLCompact = True

data Q_TYPE = Universal | Existential deriving (Eq, Ord, Show)
data PredOrFunc = Pred | Func deriving (Eq, Ord, Show)
data TextInfo = TextInfo {
    vars :: Set.Set String
  , props :: Set.Set String
  , arityPred :: MapSet String Int
  , arityFunc :: MapSet String Int
  } deriving Show

emptyTI :: TextInfo
emptyTI = TextInfo { vars = Set.empty
                   , props = Set.empty
                   , arityPred = MapSet.empty
                   , arityFunc = MapSet.empty
                   }

unionTI :: TextInfo -> TextInfo -> TextInfo
unionTI s t = TextInfo { vars = on Set.union vars s t
                       , props = on Set.union props s t
                       , arityPred = on MapSet.union arityPred s t
                       , arityFunc = on MapSet.union arityFunc s t
                       }

unionsTI :: [TextInfo] -> TextInfo
unionsTI = foldr unionTI emptyTI

removeFromTI :: String -> TextInfo -> TextInfo
removeFromTI n ti = ti { vars = Set.delete n $ vars ti
                       , props = Set.delete n $ props ti
                       , arityPred = MapSet.fromMap $
                                      Map.delete n $ MapSet.toMap $ arityPred ti
                       , arityFunc = MapSet.fromMap $
                                      Map.delete n $ MapSet.toMap $ arityFunc ti
                       }


mapSub :: ClSl.CommonLogicSL -> CSL.CASL_Sublogics
mapSub _ = CSL.caslTop
        { CSL.cons_features = CSL.emptyMapConsFeature
        , CSL.sub_features = CSL.NoSub }

mapMor :: ClMor.Morphism -> Result CMor.CASLMor
mapMor mor = Result [] $ Just (CMor.embedMorphism ()
  (mapSig emptyTI $ ClMor.source mor) $ mapSig emptyTI $ ClMor.target mor)
  { CMor.pred_map = trMor $ ClMor.propMap mor }

-- | Helper for map mor
trMor :: Map.Map Id.Id Id.Id -> Map.Map (Id.Id, CSign.PredType) Id.Id
trMor mp =
    let
        pt = CSign.PredType {CSign.predArgs = []}
    in
      Map.foldWithKey
             (\ k a ->
              Map.insert (k, pt) a
             )
      Map.empty
      mp

-- |
mapTheory :: (ClSign.Sign, [AS_Anno.Named Cl.TEXT_META])
              -> Result (CSign.CASLSign, [AS_Anno.Named CBasic.CASLFORMULA])
mapTheory (sig, form) = do
  ti <- do
    cti <- mapM (collectTextInfo . AS_Anno.sentence) form
    return $ unionsTI cti
  frm <- mapM trNamedForm form
  return (mapSig ti sig, frm)

mapSig :: TextInfo -> ClSign.Sign -> CSign.CASLSign
mapSig ti _ =
  let constOpMap = Set.fold (\ n res ->
          MapSet.insert (Id.stringToId n) (opTypeSign 0) res
        ) MapSet.empty (vars ti)
      constPredMap = Set.fold (\ n res ->
          MapSet.insert (Id.stringToId n) (predTypeSign 0) res
        ) MapSet.empty (props ti)
      opMap = MapSet.foldWithKey (\ n ar ops ->
          MapSet.insert (Id.stringToId n) (opTypeSign ar) ops
        ) MapSet.empty (arityFunc ti)
      predMap = MapSet.foldWithKey (\ n ar preds ->
          MapSet.insert (Id.stringToId n) (predTypeSign ar) preds
        ) MapSet.empty (arityPred ti)
  in CSign.uniteCASLSign (
          (CSign.emptySign ()) {
              CSign.opMap = MapSet.union constOpMap opMap
            , CSign.predMap = MapSet.union constPredMap predMap
            }
        ) caslSig

opTypeSign :: Int -> CSign.OpType
opTypeSign ar = CSign.mkTotOpType (replicate ar individual) individual

predTypeSign :: Int -> CSign.PredType
predTypeSign ar = CSign.PredType {CSign.predArgs = replicate ar individual}


-- | setting casl sign: sorts, cons, fun, nil, pred
caslSig :: CSign.CASLSign
caslSig = (CSign.emptySign ())
               { CSign.sortRel = Rel.fromKeysSet $ Set.fromList [individual] }

individual :: Id.Id
individual = Id.stringToId "individual"

trNamedForm :: AS_Anno.Named Cl.TEXT_META
            -> Result (AS_Anno.Named CBasic.CASLFORMULA)
trNamedForm = AS_Anno.mapNamedM $ trFormMeta . eliminateModules

mapSentence :: ClSign.Sign -> Cl.TEXT_META -> Result CBasic.CASLFORMULA
mapSentence _ = trFormMeta . eliminateModules

-- ignores importations
trFormMeta :: Cl.TEXT_META -> Result CBasic.CASLFORMULA
trFormMeta tm = trForm $ Cl.getText tm

trForm :: Cl.TEXT -> Result CBasic.CASLFORMULA
trForm form =
   case form of
     Cl.Text phrs rn -> do
        phrsfrm <- mapM phraseForm $ filter nonImportAndNonEmpty phrs
        return $ CBasic.conjunctRange phrsfrm rn
     Cl.Named_text _ t _ -> trForm t
   where nonImportAndNonEmpty :: Cl.PHRASE -> Bool
         nonImportAndNonEmpty p = case p of
            Cl.Importation _ -> False
            Cl.Comment_text _ t _ -> not $ isTextEmpty t
            _ -> True
         isTextEmpty :: Cl.TEXT -> Bool
         isTextEmpty txt = case txt of
            Cl.Named_text _ t _ -> isTextEmpty t
            Cl.Text [] _ -> True
            _ -> False

phraseForm :: Cl.PHRASE -> Result CBasic.CASLFORMULA
phraseForm phr = case phr of
  Cl.Module _ -> error "CL2CASLCompact.phraseForm.Module"
  -- cannot occur because module elimination applied
  Cl.Sentence s -> senForm Set.empty s
  Cl.Importation _ -> error "CL2CASLCompact.phraseForm.Importation"
  -- cannot occur, because filtered
  Cl.Comment_text _ t _ -> trForm t

senForm :: Set.Set Cl.NAME -> Cl.SENTENCE -> Result CBasic.CASLFORMULA
senForm bndVars form = case form of
  Cl.Bool_sent bs rn -> case bs of
      Cl.Negation s -> do
          sen <- senForm bndVars s
          return $ CBasic.Negation sen rn
      Cl.Junction j ss -> do
          sens <- mapM (senForm bndVars) ss
          return $ (case j of
            Cl.Conjunction -> CBasic.conjunctRange
            Cl.Disjunction -> CBasic.disjunctRange) sens rn
      Cl.BinOp j s1 s2 -> do
          sen1 <- senForm bndVars s1
          sen2 <- senForm bndVars s2
          return $ CBasic.Relation sen1 (case j of
            Cl.Implication -> CBasic.Implication
            Cl.Biconditional -> CBasic.Equivalence) sen2 rn
  Cl.Quant_sent q bs s rn ->
        quantSentForm (case q of
          Cl.Universal -> Universal
          Cl.Existential -> Existential) rn bndVars bs s
  Cl.Atom_sent at rn -> case at of
      Cl.Equation trm1 trm2 -> do
          t1 <- termForm bndVars $ uncurryTerm trm1
          t2 <- termForm bndVars $ uncurryTerm trm2
          return $ CBasic.Equation t1 CBasic.Strong t2 rn
      Cl.Atom trm tseqs -> do
          trmFP <- termFormPrd (uncurryTerm trm) (length tseqs)
          trmSeqs <- mapM (termSeqForm bndVars) tseqs
          return $ CBasic.Predication trmFP trmSeqs rn
  Cl.Comment_sent _ s _ -> senForm bndVars s
  Cl.Irregular_sent s _ -> senForm bndVars s

-- checks for second order quantification
quantSentForm :: Q_TYPE -> Id.Range -> Set.Set Cl.NAME -> [Cl.NAME_OR_SEQMARK]
                 -> Cl.SENTENCE -> Result CBasic.CASLFORMULA
quantSentForm qt rn bndVars bs sen = do
  ti <- colTiSen sen
  bSs <- mapM nosStrnig bs
  let (predSs, opsVars) = partition
          (\ n -> Map.member n $ MapSet.toMap $ arityPred ti) bSs
  let (opSs, predsVars) = partition
          (\ n -> Map.member n $ MapSet.toMap $ arityFunc ti) bSs
  let vs = map (Cl.Name . Id.mkSimpleId) $ intersect opsVars predsVars
  let preds = MapSet.filterWithKey (\ s _ -> elem s predSs) $ arityPred ti
  let ops = MapSet.filterWithKey (\ s _ -> elem s opSs) $ arityFunc ti
  let quantifier = case qt of
          Universal -> CBasic.Universal
          Existential -> CBasic.Existential
  bndVarsSet <- bndVarsToSet bndVars vs
  folSen <- if null vs
            then senForm bndVars sen
            else do
              sf <- senForm bndVarsSet sen
              bindSeq <- mapM bindingSeq bs
              return $ CBasic.Quantification quantifier
                         [CBasic.Var_decl bindSeq individual Id.nullRange] sf rn
  let predSen = MapSet.foldWithKey (\ prd ar s ->
          CBasic.QuantPred (Id.stringToId prd) (predType ar) s
        ) folSen preds
  let opSen = MapSet.foldWithKey (\ op ar s ->
          CBasic.QuantOp (Id.stringToId op) (opType ar) s
        ) predSen ops
  return opSen

opType :: Int -> CBasic.OP_TYPE
opType ar =
  CBasic.Op_type CBasic.Total (replicate ar individual) individual Id.nullRange

predType :: Int -> CBasic.PRED_TYPE
predType ar = CBasic.Pred_type (replicate ar individual) Id.nullRange

bndVarsToSet :: Set.Set Cl.NAME -> [Cl.NAME_OR_SEQMARK]
  -> Result (Set.Set Cl.NAME)
bndVarsToSet bndVars bs = do
  res <- mapM (\ nos -> case nos of
                  Cl.Name n -> return n
                  Cl.SeqMark s -> fail $ errSeqMark s)
        bs
  return $ foldr Set.insert bndVars res

termForm :: Set.Set Cl.NAME -> Cl.TERM -> Result (CBasic.TERM a)
termForm bndVars trm = case trm of
  Cl.Name_term n ->
      if Set.member n bndVars
      then return $ CBasic.Qual_var n individual Id.nullRange
      else do
        trmFA <- termFormApp trm 0
        return $ CBasic.Application trmFA [] Id.nullRange
  Cl.Funct_term term tseqs rn -> do
      trmFA <- termFormApp term (length tseqs)
      trmSF <- mapM (termSeqForm bndVars) tseqs
      return $ CBasic.Application trmFA trmSF rn
  Cl.Comment_term term _ _ -> termForm bndVars (uncurryTerm term)
  Cl.That_term {} -> fail "CommonLogic2CASLCompact.termForm"

termFormApp :: Cl.TERM -> Int -> Result CBasic.OP_SYMB
termFormApp trm ar = case trm of
  Cl.Name_term n ->
      return $ CBasic.Qual_op_name (Id.mkId [n]) (opType ar) Id.nullRange
  Cl.Comment_term t _ _ -> termFormApp t ar
  _ -> fail errCurriedFunctionS

termFormPrd :: Cl.TERM -> Int -> Result CBasic.PRED_SYMB
termFormPrd trm ar = case trm of
  Cl.Name_term n ->
      return $ CBasic.Qual_pred_name (Id.mkId [n]) (predType ar) Id.nullRange
  Cl.Comment_term t _ _ -> termFormPrd t ar
  Cl.Funct_term {} -> fail $ errFunctionReturnedPredicateS trm
  Cl.That_term {} -> fail "CommonLogic2CASLCompact.termFormPrd"

termSeqForm :: Set.Set Cl.NAME -> Cl.TERM_SEQ -> Result (CBasic.TERM a)
termSeqForm bndVars tseq = case tseq of
  Cl.Term_seq trm -> termForm bndVars $ uncurryTerm trm
  Cl.Seq_marks s -> fail $ errSeqMark s

bindingSeq :: Cl.NAME_OR_SEQMARK -> Result CBasic.VAR
bindingSeq bs = case bs of
  Cl.Name n -> return n
  Cl.SeqMark s -> fail $ errSeqMark s

collectTextInfo :: Cl.TEXT_META -> Result TextInfo
collectTextInfo tm = colTiTxt $ Cl.getText tm

colTiTxt :: Cl.TEXT -> Result TextInfo
colTiTxt txt = case txt of
  Cl.Named_text _ t _ -> colTiTxt t
  Cl.Text ps _ -> do
    cti <- mapM colTiPhr ps
    return $ unionsTI cti

colTiPhr :: Cl.PHRASE -> Result TextInfo
colTiPhr p = case p of
  Cl.Module (Cl.Mod _ t _) -> colTiTxt t
  Cl.Module (Cl.Mod_ex _ _ t _) -> colTiTxt t
  Cl.Importation _ -> return emptyTI
  Cl.Comment_text _ t _ -> colTiTxt t
  Cl.Sentence s -> colTiSen s

colTiSen :: Cl.SENTENCE -> Result TextInfo
colTiSen sen = case sen of
  Cl.Quant_sent _ noss s _ -> do
          cti <- colTiSen s
          nossR <- mapM nosStrnig noss
          return $ foldr removeFromTI cti nossR
  Cl.Bool_sent b _ -> case b of
      Cl.Junction _ sens -> do
          cti <- mapM colTiSen sens
          return $ unionsTI cti
      Cl.Negation s -> colTiSen s
      Cl.BinOp _ s1 s2 -> do
          cti <- mapM colTiSen [s1, s2]
          return $ unionsTI cti
  Cl.Atom_sent a _ -> case a of
      Cl.Equation t1 t2 -> do
          cti <- mapM (colTiTrmVar . uncurryTerm) [t1, t2]
          return $ unionsTI cti
      Cl.Atom t [] -> colTiTrmProp $ uncurryTerm t
      Cl.Atom t tseqs -> colTiAddArity Pred (uncurryTerm t) tseqs
  Cl.Comment_sent _ s _ -> colTiSen s
  Cl.Irregular_sent s _ -> colTiSen s

nosStrnig :: Cl.NAME_OR_SEQMARK -> Result String
nosStrnig nos = case nos of
  Cl.Name n -> return $ Id.tokStr n
  Cl.SeqMark s -> fail $ errSeqMark s

colTiTrmVar :: Cl.TERM -> Result TextInfo
colTiTrmVar trm = case trm of
  Cl.Name_term n -> return $ emptyTI {vars = Set.singleton (Id.tokStr n)}
  Cl.Comment_term t _ _ -> colTiTrmVar t
  _ -> colTiTrm $ uncurryTerm trm

colTiTrmProp :: Cl.TERM -> Result TextInfo
colTiTrmProp trm = case trm of
  Cl.Name_term n -> return $ emptyTI {props = Set.singleton (Id.tokStr n)}
  Cl.Comment_term t _ _ -> colTiTrmProp t
  _ -> colTiTrm $ uncurryTerm trm

colTiTrm :: Cl.TERM -> Result TextInfo
colTiTrm trm = case trm of
  Cl.Name_term _ -> return emptyTI
  Cl.Funct_term t tseqs _ -> colTiAddArity Func t tseqs
  Cl.Comment_term t _ _ -> colTiTrm $ uncurryTerm t
  Cl.That_term {} -> fail "CommonLogic2CASLCompact.colTiTrm"

colTiTrmSeq :: Cl.TERM_SEQ -> Result TextInfo
colTiTrmSeq tseq = case tseq of
  Cl.Term_seq trm -> colTiTrmVar trm
  Cl.Seq_marks s -> fail $ errSeqMark s

colTiAddArity :: PredOrFunc -> Cl.TERM -> [Cl.TERM_SEQ] -> Result TextInfo
colTiAddArity ty trm tseqs = case trm of
  Cl.Name_term n -> do
      cti <- mapM colTiTrmSeq tseqs
      return $ unionsTI
             $ ( if ty == Pred
                  then emptyTI { arityPred = MapSet.insert
                                  (Id.tokStr n) (length tseqs) MapSet.empty}
                  else emptyTI { arityFunc = MapSet.insert
                                  (Id.tokStr n) (length tseqs) MapSet.empty}
                  ) : cti
  Cl.Funct_term {} -> colTiTrm $ uncurryTerm trm -- FIX predicate "(f x) y"
  Cl.Comment_term t _ _ -> colTiAddArity ty t tseqs
  Cl.That_term {} -> fail "CommonLogic2CASLCompact.colTiAddArity"

{- If curried, uncurries term. Otherwise original term returned
removes comments -}
uncurryTerm :: Cl.TERM -> Cl.TERM
uncurryTerm trm = case trm of
  Cl.Funct_term t tseqs rn ->
      let (nt, args) = uncurryTermWithArgs t tseqs in
      Cl.Funct_term nt args rn
  Cl.Comment_term t _ _ -> uncurryTerm t
  _ -> trm

uncurryTermWithArgs :: Cl.TERM -> [Cl.TERM_SEQ] -> (Cl.TERM, [Cl.TERM_SEQ])
uncurryTermWithArgs trm tseqs = case trm of
  Cl.Funct_term t ts _ -> uncurryTermWithArgs t (ts ++ tseqs)
  Cl.Comment_term t _ _ -> uncurryTermWithArgs t tseqs
  _ -> (trm, tseqs)

errSeqMark :: Cl.SEQ_MARK -> String
errSeqMark s = "Comorphism CommonLogic2CASLCompact error: "
  ++ "Sequence marks not allowed in this comorphism. Found: " ++ Id.tokStr s

errCurriedFunctionS :: String
errCurriedFunctionS = "Comorphism CommonLogic2CASLCompact error: "
  ++ "Found curried function"

errFunctionReturnedPredicateS :: Cl.TERM -> String
errFunctionReturnedPredicateS t = "Comorphism CommonLogic2CASLCompact error: "
  ++ "Function returned predicate " ++ show (pretty t)
