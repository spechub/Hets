{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./Comorphisms/CommonLogic2CASL.hs
Description :  Comorphism from CommonLogic to CASL
Copyright   :  (c)  Eugen Kuksa, Uni Bremen 2011, DFKI GmbH 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (via Logic.Logic)

Translating comorphism from Common Logic
(with and without sequence markers) to CASL

-}

module Comorphisms.CommonLogic2CASL
  ( CL2CFOL (..)
  ) where

import Logic.Logic as Logic
import Logic.Comorphism

import Common.ProofTree
import Common.Token
import Common.Result
import Common.AS_Annotation as AS_Anno
import Common.Lib.MapSet (MapSet)
import qualified Common.Lib.MapSet as MapSet
import qualified Common.Lib.Rel as Rel
import Common.Id

import Data.Function (on)
import qualified Data.Set as Set
import qualified Data.Map as Map

-- Common Logic
import qualified CommonLogic.Logic_CommonLogic as ClLogic
import qualified CommonLogic.AS_CommonLogic as Cl
import qualified CommonLogic.Sign as ClSign
import qualified CommonLogic.Symbol as ClSymbol
import qualified CommonLogic.Morphism as ClMor
import CommonLogic.Sublogic as ClSl
import CommonLogic.PredefinedCASLAxioms
import CommonLogic.ModuleElimination

-- CASL
import qualified CASL.Logic_CASL as CLogic
import CASL.AS_Basic_CASL as CBasic
import qualified CASL.Sublogic as CSL
import CASL.Sign as CSign
import CASL.Morphism as CMor

import qualified Control.Monad.Fail as Fail

newtype CL2CFOL = CL2CFOL { fol :: CommonLogicSL } deriving Show

showCLTextType :: Bool -> CLTextType -> String
showCLTextType b s = case s of
  FirstOrder -> if b then "Fol" else "Seq"
  Impredicative -> if b then "Imp" else "Full"
  _ -> show s ++ if b then "Compact" else ""

instance Language CL2CFOL where
  language_name (CL2CFOL b) = "CL"
    ++ showCLTextType (compact b) (format b) ++ "2CFOL"

instance Comorphism
    CL2CFOL -- comorphism
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
      sourceLogic (CL2CFOL _) = ClLogic.CommonLogic
      sourceSublogic (CL2CFOL b) = b
      targetLogic (CL2CFOL _) = CLogic.CASL
      mapSublogic (CL2CFOL _) = Just . mapSub
      map_theory (CL2CFOL b) = mapTheory b
      map_morphism (CL2CFOL b) = mapMor b
      map_sentence (CL2CFOL b) _ = mapSentence b
      has_model_expansion (CL2CFOL _) = True

data PredOrFunc = Pred | Func deriving (Eq, Ord, Show)

data TextInfo = TextInfo
  { arityPred :: MapSet String Int
  , arityFunc :: MapSet String Int
  , boundPred :: MapSet String Int
  , boundFunc :: MapSet String Int
  , seqMarkers :: Set.Set String
  } deriving Show

emptyTI :: TextInfo
emptyTI = TextInfo
  { arityPred = MapSet.empty
  , arityFunc = MapSet.empty
  , boundPred = MapSet.empty
  , boundFunc = MapSet.empty
  , seqMarkers = Set.empty
  }

unionTI :: TextInfo -> TextInfo -> TextInfo
unionTI s t = TextInfo
  { arityPred = on MapSet.union arityPred s t
  , arityFunc = on MapSet.union arityFunc s t
  , boundPred = on MapSet.union boundPred s t
  , boundFunc = on MapSet.union boundFunc s t
  , seqMarkers = on Set.union seqMarkers s t
  }

unionsTI :: [TextInfo] -> TextInfo
unionsTI = foldr unionTI emptyTI

removeFromTI :: String -> TextInfo -> TextInfo
removeFromTI n ti = let deln = MapSet.fromMap . Map.delete n . MapSet.toMap in
  ti
  { arityPred = deln $ arityPred ti
  , arityFunc = deln $ arityFunc ti
  , seqMarkers = Set.delete n $ seqMarkers ti
  }

mapSub :: ClSl.CommonLogicSL -> CSL.CASL_Sublogics
mapSub _ = CSL.cFol
        { CSL.cons_features = CSL.emptyMapConsFeature }

-- unsuitable, mere signatures cannot be mapped properly!
mapMor :: CommonLogicSL -> ClMor.Morphism -> Result CMor.CASLMor
mapMor b mor = return (CMor.embedMorphism ()
  (mapSig b emptyTI) $ mapSig b emptyTI)
  { CMor.pred_map = trMor $ ClMor.propMap mor }

-- | Helper for map mor
trMor :: Map.Map Id Id -> Map.Map (Id, PredType) Id
trMor mp =
    let
        pt = PredType {predArgs = []}
        id2Id = tok2Id . mkSimpleId . show
    in
      Map.foldrWithKey
             (\ k a ->
              Map.insert (id2Id k, pt) $ id2Id a
             )
      Map.empty
      mp

mapTheory :: CommonLogicSL -> (ClSign.Sign, [AS_Anno.Named Cl.TEXT_META])
              -> Result (CASLSign, [AS_Anno.Named CBasic.CASLFORMULA])
mapTheory b (_, form) = do
  ti <- fmap unionsTI $ mapM (collectTextInfo . AS_Anno.sentence) form
  frm <- mapM (trNamedForm b) form
  let s = mapSig b ti
  return $ if compact b then (s, frm) else
    (uniteCASLSign listSig s, baseListAxioms ++ frm)

funS :: String
funS = "fun"

relS :: String
relS = "rel"

seqType :: OpType
seqType = mkTotOpType [list] individual

seqFunType :: OpType
seqFunType = mkTotOpType [individual, list] individual

seqRelType :: PredType
seqRelType = PredType [individual, list]

mapNs :: Ord a => MapSet String a -> MapSet Id a
mapNs = MapSet.foldWithKey (MapSet.insert . stringToId) MapSet.empty

mapSig :: CommonLogicSL -> TextInfo -> CASLSign
mapSig b ti =
  let isFol = format b <= FirstOrder
      isC = compact b
      aF = arityFunc ti
      (aC, aRF) = MapSet.partition (== 0) aF
      aA = MapSet.union aF aP
      collM n = MapSet.fromMap . Map.singleton n . Set.map (+ 1) . MapSet.elems
      om = if isC then
        MapSet.foldWithKey (\ n ar ops ->
          MapSet.insert (stringToId n) (opTypeSign ar) ops
        ) MapSet.empty
          $ if isFol then aF else
              MapSet.union (MapSet.mapSet (const $ Set.singleton 0) aA)
              $ collM funS $ MapSet.mapSet (Set.delete 0) $ boundFunc ti
        else mapNs
             $ MapSet.union
               (if isFol then
                 MapSet.mapSet (const $ Set.singleton seqType) aRF
               else MapSet.insert funS seqFunType MapSet.empty)
             $ MapSet.union (MapSet.mapSet (const $ Set.singleton
               $ mkTotOpType [] individual) $ if isFol then aC else aA)
             $ MapSet.fromList
             $ map (\ s -> (s, [mkTotOpType [] list]))
             $ Set.toList $ seqMarkers ti
      aP = arityPred ti
      pm | isC =
            MapSet.foldWithKey (\ n ar preds ->
            MapSet.insert (stringToId n) (predTypeSign ar) preds
            ) MapSet.empty $ if isFol then aP else collM relS $ boundPred ti
         | isFol = mapNs $ MapSet.mapSet (const $ Set.singleton
            $ PredType [list]) aP
         | otherwise = MapSet.insert (stringToId relS) seqRelType MapSet.empty
  in (emptySign ())
            { sortRel = Rel.insertKey individual Rel.empty
            , opMap = om
            , predMap = pm
            }

opTypeSign :: Int -> OpType
opTypeSign ar = mkTotOpType (replicate ar individual) individual

predTypeSign :: Int -> PredType
predTypeSign ar = PredType {predArgs = replicate ar individual}

trNamedForm :: CommonLogicSL -> AS_Anno.Named Cl.TEXT_META
            -> Result (AS_Anno.Named CBasic.CASLFORMULA)
trNamedForm b = AS_Anno.mapNamedM $ trFormMeta b . eliminateModules

mapSentence :: CommonLogicSL -> Cl.TEXT_META -> Result CBasic.CASLFORMULA
mapSentence b = trFormMeta b . eliminateModules

-- ignores importations
trFormMeta :: CommonLogicSL -> Cl.TEXT_META -> Result CBasic.CASLFORMULA
trFormMeta b tm = trForm b $ Cl.getText tm

trForm :: CommonLogicSL -> Cl.TEXT -> Result CBasic.CASLFORMULA
trForm b form =
   case form of
     Cl.Text phrs rn -> do
        phrsfrm <- mapM (phraseForm b) $ filter nonImportAndNonEmpty phrs
        return $ CBasic.conjunctRange phrsfrm rn
     Cl.Named_text _ t _ -> trForm b t
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

phraseForm :: CommonLogicSL -> Cl.PHRASE -> Result CBasic.CASLFORMULA
phraseForm b phr = case phr of
  Cl.Module _ -> error "CL2CFOL.phraseForm.Module"
  -- cannot occur because module elimination applied
  Cl.Sentence s -> senForm b Set.empty s
  Cl.Importation _ -> error "CL2CFOL.phraseForm.Importation"
  -- cannot occur, because filtered
  Cl.Comment_text _ t _ -> trForm b t

senForm :: CommonLogicSL -> Set.Set Cl.NAME -> Cl.SENTENCE
  -> Result CBasic.CASLFORMULA
senForm b bndVars form = case form of
  Cl.Bool_sent bs rn -> case bs of
      Cl.Negation s -> do
          sen <- senForm b bndVars s
          return $ CBasic.Negation sen rn
      Cl.Junction j ss -> do
          sens <- mapM (senForm b bndVars) ss
          return $ (case j of
            Cl.Conjunction -> CBasic.conjunctRange
            Cl.Disjunction -> CBasic.disjunctRange) sens rn
      Cl.BinOp j s1 s2 -> do
          sen1 <- senForm b bndVars s1
          sen2 <- senForm b bndVars s2
          return $ CBasic.Relation sen1 (case j of
            Cl.Implication -> CBasic.Implication
            Cl.Biconditional -> CBasic.Equivalence) sen2 rn
  Cl.Quant_sent q bs s rn ->
        quantSentForm b (case q of
          Cl.Universal -> CBasic.Universal
          Cl.Existential -> CBasic.Existential) rn bndVars bs s
  Cl.Atom_sent at rn -> case at of
      Cl.Equation trm1 trm2 -> do
          t1 <- termForm b bndVars trm1
          t2 <- termForm b bndVars trm2
          return $ CBasic.Equation t1 CBasic.Strong t2 rn
      Cl.Atom trm tseqs -> do
          let (rt, rseq) = uncurryTermWithArgs trm tseqs
          trmSeqs <- termSeq b bndVars rseq
          let ar = length rseq
              isC = compact b
          if format b <= FirstOrder then do
              trmFP <- termFormPrd rt
                $ if isC then Just ar else Nothing
              return $ CBasic.Predication trmFP trmSeqs rn
            else do
              trm1 <- termForm b bndVars rt
              return $ CBasic.Predication
                (CBasic.mkQualPred (stringToId relS)
                $ if isC then predType $ ar + 1 else toPRED_TYPE seqRelType)
                (trm1 : trmSeqs) rn
  Cl.Comment_sent _ s _ -> senForm b bndVars s
  Cl.Irregular_sent s _ -> senForm b bndVars s

-- checks for second order quantification
quantSentForm :: CommonLogicSL -> QUANTIFIER -> Range -> Set.Set Cl.NAME
  -> [Cl.NAME_OR_SEQMARK] -> Cl.SENTENCE -> Result CBasic.CASLFORMULA
quantSentForm b quantifier rn bndVars bs sen = do
  folSen <- if null bs
            then senForm b bndVars sen
            else do
              bndVarsSet <- bndVarsToSet bndVars bs
              sf <- senForm b bndVarsSet sen
              bindSeq <- mapM bindingSeq bs
              return $ CBasic.Quantification quantifier bindSeq sf rn
  return folSen

opType :: Int -> CBasic.OP_TYPE
opType ar =
  CBasic.Op_type CBasic.Total (replicate ar individual) individual nullRange

predType :: Int -> CBasic.PRED_TYPE
predType ar = CBasic.Pred_type (replicate ar individual) nullRange

bndVarsToSet :: Set.Set Cl.NAME -> [Cl.NAME_OR_SEQMARK]
  -> Result (Set.Set Cl.NAME)
bndVarsToSet bndVars bs = do
  res <- mapM (\ nos -> return $ case nos of
                  Cl.Name n -> n
                  Cl.SeqMark s -> s)
        bs
  return $ foldr Set.insert bndVars res

termForm :: CommonLogicSL -> Set.Set Cl.NAME -> Cl.TERM
  -> Result (CBasic.TERM ())
termForm b bndVars trm = case trm of
  Cl.Name_term n ->
      if Set.member n bndVars
      then return $ CBasic.Qual_var (mkSimpleId $ tok2Str n)
        individual nullRange
      else do
        trmFA <- termFormApp trm (Just 0)
        return $ CBasic.Application trmFA [] nullRange
  Cl.Funct_term oterm oseq rn -> do
      let (term, tseqs) = uncurryTermWithArgs oterm oseq
      let ar = length tseqs
          isC = compact b
      trmSF <- termSeq b bndVars tseqs
      if format b <= FirstOrder then do
         trmFA <- termFormApp term $ if isC then Just ar else Nothing
         return $ CBasic.Application trmFA trmSF rn
        else do
         trm1 <- termForm b bndVars term
         return $ CBasic.Application
            (CBasic.mkQualOp (stringToId funS) $ if isC then opType $ ar + 1
              else toOP_TYPE seqFunType)
            (trm1 : trmSF) rn
  Cl.Comment_term term _ _ -> termForm b bndVars term
  Cl.That_term {} -> Fail.fail "CL2CFOL: that-terms not supported"

termFormApp :: Cl.TERM -> Maybe Int -> Result CBasic.OP_SYMB
termFormApp trm ar = case trm of
  Cl.Name_term n -> return $ mkQualOp (tok2Id n) $ maybe (toOP_TYPE seqType)
     opType ar
  Cl.Comment_term t _ _ -> termFormApp t ar
  _ -> Fail.fail "CL2CFOL.termFormApp"

termFormPrd :: Cl.TERM -> Maybe Int -> Result CBasic.PRED_SYMB
termFormPrd trm ar = case trm of
  Cl.Name_term n -> return $ mkQualPred (tok2Id n) $ maybe
    (Pred_type [list] nullRange) predType ar
  Cl.Comment_term t _ _ -> termFormPrd t ar
  _ -> Fail.fail "CL2CFOL.termFormPrd"

termSeqForm :: CommonLogicSL -> Set.Set Cl.NAME -> Cl.TERM_SEQ
  -> Result (CBasic.TERM ())
termSeqForm b bndVars tseq = case tseq of
  Cl.Term_seq trm -> termForm b bndVars trm
  Cl.Seq_marks s -> return $ mkVarTerm (mkSimpleId $ tok2Str s) list

termSeq, mapTermSeq, foldTermSeq :: CommonLogicSL -> Set.Set Cl.NAME
  -> [Cl.TERM_SEQ] -> Result [CBasic.TERM ()]
termSeq b = if compact b then mapTermSeq b else foldTermSeq b

mapTermSeq b bndVars = mapM (termSeqForm b bndVars)

foldTermSeq b bndVars = fmap (: []) . foldr (fTermSeq b bndVars) (return mkNil)

fTermSeq :: CommonLogicSL -> Set.Set Cl.NAME -> Cl.TERM_SEQ
  -> Result (CBasic.TERM ()) -> Result (CBasic.TERM ())
fTermSeq b bndVars tseq r = do
  l <- r
  case tseq of
   Cl.Term_seq trm -> do
     i <- termForm b bndVars trm
     return $ mkCons i l
   Cl.Seq_marks s ->
     let e = mkVarTerm (mkSimpleId $ tok2Str s) list
     in return $ if l == mkNil then e else mkAppend e l

bindingSeq :: Cl.NAME_OR_SEQMARK -> Result CBasic.VAR_DECL
bindingSeq bs = return $ case bs of
  Cl.Name n -> mkVarDecl (mkSimpleId $ tok2Str n) individual
  Cl.SeqMark s -> mkVarDecl (mkSimpleId $ tok2Str s) list

collectTextInfo :: Cl.TEXT_META -> Result TextInfo
collectTextInfo tm = colTiTxt $ Cl.getText tm

tok2Id :: Token -> Id
tok2Id = stringToId . tok2Str

tok2Str :: Token -> String
tok2Str t = let
  r = concatMap (\ c -> if c == 'x' then [c, c] else [c])
    $ tokStr t
  (d, u) = span (== '.') r
  s = if null d then u else 'x' : show (length d) ++ u
  in if elem s casl_reserved_fwords then "x_" ++ s else s

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
          nossR <- mapM nosString noss
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
          cti <- mapM colTiTrm [t1, t2]
          return $ unionsTI cti
      Cl.Atom t tseqs -> let (rt, rseq) = uncurryTermWithArgs t tseqs in
          colTiAddArity Pred rt rseq
  Cl.Comment_sent _ s _ -> colTiSen s
  Cl.Irregular_sent s _ -> colTiSen s

nosString :: Cl.NAME_OR_SEQMARK -> Result String
nosString nos = return . tok2Str $ case nos of
  Cl.Name n -> n
  Cl.SeqMark s -> s

colTiTrm :: Cl.TERM -> Result TextInfo
colTiTrm trm = case trm of
  Cl.Name_term n -> let m = MapSet.insert (tok2Str n) 0 MapSet.empty in
    return $ emptyTI
      { arityFunc = m
      , boundFunc = m }
  Cl.Funct_term t tseqs _ -> let (rt, rseq) = uncurryTermWithArgs t tseqs in
      colTiAddArity Func rt rseq
  Cl.Comment_term t _ _ -> colTiTrm t
  Cl.That_term s _ -> colTiSen s

colTiTrmSeq :: Cl.TERM_SEQ -> Result TextInfo
colTiTrmSeq tseq = case tseq of
  Cl.Term_seq trm -> colTiTrm trm
  Cl.Seq_marks s -> return $ emptyTI
    { seqMarkers = Set.singleton (tok2Str s) }

colTiAddArity :: PredOrFunc -> Cl.TERM -> [Cl.TERM_SEQ] -> Result TextInfo
colTiAddArity ty trm tseqs = case trm of
  Cl.Name_term n -> do
    cti <- mapM colTiTrmSeq tseqs
    let m = MapSet.insert (tok2Str n) (length tseqs) MapSet.empty
    return $ unionsTI
             $ ( if ty == Pred
                  then emptyTI { arityPred = m
                               , boundPred = m }
                  else emptyTI { arityFunc = m
                               , boundFunc = m }
                  ) : cti
  _ -> do
    cti <- mapM colTiTrmSeq tseqs
    ti <- colTiTrm trm
    return . unionsTI $ ti : cti

{- If curried, uncurries term. Otherwise original term returned
removes comments -}

uncurryTermWithArgs :: Cl.TERM -> [Cl.TERM_SEQ] -> (Cl.TERM, [Cl.TERM_SEQ])
uncurryTermWithArgs trm tseqs = case trm of
  Cl.Funct_term t ts _ -> uncurryTermWithArgs t (ts ++ tseqs)
  Cl.Comment_term t _ _ -> uncurryTermWithArgs t tseqs
  _ -> (trm, tseqs)
