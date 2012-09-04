{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
Copyright   :  (c) Klaus Luettich, Uni Bremen 2004, DFKI GmbH 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The possible world encoding comorphism from ModalCASL to CASL.

   We use the Relational Translation by adding one extra parameter of
   type world to each predicate.

-}

module Comorphisms.Modal2CASL (Modal2CASL (..)) where

import Logic.Logic
import Logic.Comorphism

import Common.AS_Annotation
import Common.Id
import Common.ProofTree
import qualified Common.Lib.MapSet as MapSet
import qualified Common.Lib.Rel as Rel

-- CASL
import CASL.Logic_CASL
import CASL.Sublogic as SL
import CASL.Sign
import CASL.AS_Basic_CASL
import CASL.Morphism
import CASL.Utils

-- ModalCASL
import Modal.Logic_Modal
import Modal.AS_Modal
import Modal.ModalSign
import Modal.Utils

-- generated function
import Modal.ModalSystems

import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Maybe
import Control.Exception (assert)


-- | The identity of the comorphism
data Modal2CASL = Modal2CASL deriving (Show)

instance Language Modal2CASL -- default definition is okay

instance Comorphism Modal2CASL
               Modal ()
               M_BASIC_SPEC ModalFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               MSign
               ModalMor
               Symbol RawSymbol ()
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               Symbol RawSymbol ProofTree where
    sourceLogic Modal2CASL = Modal
    sourceSublogic Modal2CASL = ()
    targetLogic Modal2CASL = CASL
    mapSublogic Modal2CASL _ = Just SL.caslTop
    map_theory (Modal2CASL) (sig, sens) = case transSig sig of
      mme -> return (caslSign mme, relFormulas mme
                     ++ map (mapNamed $ transSen sig) sens)
    map_morphism Modal2CASL = return . mapMor
    map_sentence Modal2CASL sig = return . transSen sig
    map_symbol Modal2CASL _ = Set.singleton . mapSym
    has_model_expansion Modal2CASL = True
    is_weakly_amalgamable Modal2CASL = True

data ModName = SimpleM SIMPLE_ID
             | SortM SORT
               deriving (Show, Ord, Eq)

-- | relations on possible worlds
type ModalityRelMap = Map.Map ModName PRED_NAME

data ModMapEnv = MME
    { caslSign :: CASLSign
    , worldSort :: SORT
    , modalityRelMap :: ModalityRelMap
    , flexiOps :: OpMap
    , flexiPreds :: PredMap
    , relFormulas :: [Named CASLFORMULA] }

transSig :: MSign -> ModMapEnv
transSig sign =
   let sorSet = sortSet sign
       fws = freshWorldSort sorSet
       flexOps' = MapSet.fromMap . Map.foldWithKey (addWorld_OP fws)
                                    Map.empty $ MapSet.toMap flexibleOps
       flexPreds' = MapSet.fromMap . addWorldRels True relsTermMod
                    . addWorldRels False relsMod
                    . Map.foldWithKey (addWorld_PRED fws)
                                    Map.empty $ MapSet.toMap flexiblePreds
       flexibleOps = flexOps $ extendedInfo sign
       flexiblePreds = flexPreds $ extendedInfo sign
       rigOps' = diffOpMapSet (opMap sign) flexibleOps
       rigPreds' = diffMapSet (predMap sign) flexiblePreds
       relations = Map.union relsMod relsTermMod
       genRels f = Map.foldWithKey (\ me _ nm -> f me nm) Map.empty
       genModFrms f = Map.foldWithKey f []
       relSymbS me = Id [mkSimpleId "g_R"] [mkId [me]] nullRange
       relSymbT me = Id [mkSimpleId "g_R_t"] [me] nullRange
       relsMod = genRels (\ me nm -> Map.insert (SimpleM me) (relSymbS me) nm)
                         (modies $ extendedInfo sign)
       relsTermMod = genRels (\ me nm ->
                                  Map.insert (SortM me) (relSymbT me) nm)
                             (termModies $ extendedInfo sign)
       relModFrms = genModFrms (\ me frms trFrms -> trFrms ++
                                         transSchemaMFormulas partMME
                                                  fws (relSymbS me) frms)
                               (modies $ extendedInfo sign)
       relTermModFrms = genModFrms (\ me frms trFrms -> trFrms ++
                                         transSchemaMFormulas partMME
                                                  fws (relSymbT me) frms)
                               (termModies $ extendedInfo sign)
       addWorldRels isTermMod rels mp =
              let argSorts rs = if isTermMod
                             then [getModTermSort rs, fws, fws]
                             else [fws, fws] in
               Map.fold (\ rs nm -> Map.insert rs
                                              (Set.singleton $
                                                    PredType $ argSorts rs)
                                              nm)
                        mp rels
       partMME = MME {caslSign =
            (emptySign ())
               { sortRel = Rel.insertKey fws $ sortRel sign
               , opMap = addOpMapSet flexOps' rigOps'
               , assocOps = diffOpMapSet (assocOps sign) flexibleOps
               , predMap = addMapSet flexPreds' rigPreds'},
         worldSort = fws,
         modalityRelMap = relations,
         flexiOps = flexibleOps,
         flexiPreds = flexiblePreds,
         relFormulas = []}
      in partMME { relFormulas = relModFrms ++ relTermModFrms}

mapMor :: ModalMor -> CASLMor
mapMor m = (embedMorphism ()
    (caslSign $ transSig $ msource m)
    $ caslSign $ transSig $ mtarget m)
  { sort_map = sort_map m
  , op_map = op_map m
  , pred_map = pred_map m }

mapSym :: Symbol -> Symbol
mapSym = id  -- needs to be changed once modal symbols are added

transSchemaMFormulas :: ModMapEnv -> SORT -> PRED_NAME
                     -> [AnModFORM] -> [Named CASLFORMULA]
transSchemaMFormulas mapEnv fws relSymb =
    mapMaybe (transSchemaMFormula (mapTERM mapEnv) fws relSymb worldVars)

transSen :: MSign -> ModalFORMULA -> CASLFORMULA
transSen msig = mapSenTop (transSig msig)

mapSenTop :: ModMapEnv -> ModalFORMULA -> CASLFORMULA
mapSenTop mapEnv@(MME {worldSort = fws}) f =
    case f of
    Quantification q@Universal vs frm ps ->
        Quantification q (qwv : vs) (mapSen mapEnv wvs frm) ps
    f1 -> Quantification Universal [qwv] (mapSen mapEnv wvs f1) nullRange
    where qwv = Var_decl wvs fws nullRange
          wvs = [head worldVars]


-- head [VAR] is always the current world variable (for predication)
mapSen :: ModMapEnv -> [VAR] -> ModalFORMULA -> CASLFORMULA
mapSen mapEnv@(MME {worldSort = fws, flexiPreds = fPreds}) vars
       f = case f of
           Quantification q vs frm ps ->
                  Quantification q vs (mapSen mapEnv vars frm) ps
           Junction j fs ps ->
               Junction j (map (mapSen mapEnv vars) fs) ps
           Relation f1 c f2 ps ->
               Relation (mapSen mapEnv vars f1) c (mapSen mapEnv vars f2) ps
           Negation frm ps -> Negation (mapSen mapEnv vars frm) ps
           Atom b ps -> Atom b ps
           Equation t1 e t2 ps -> Equation
               (mapTERM mapEnv vars t1) e (mapTERM mapEnv vars t2) ps
           Predication pn as qs ->
               let as' = map (mapTERM mapEnv vars) as
                   fwsTerm = sortedWorldTerm fws (head vars)
                   (pn', as'') =
                       case pn of
                       Pred_name _ -> error "Modal2CASL: untyped predication"
                       Qual_pred_name prn pType@(Pred_type sorts pps) ps ->
                         let addTup = (Qual_pred_name (addPlace prn)
                                             (Pred_type (fws : sorts) pps) ps,
                                       fwsTerm : as')
                             defTup = (pn, as') in
                                 if Set.member (toPredType pType)
                                     $ MapSet.lookup prn fPreds
                                     then addTup
                                     else defTup
               in Predication pn' as'' qs
           Definedness t ps -> Definedness (mapTERM mapEnv vars t) ps
           Membership t ty ps -> Membership (mapTERM mapEnv vars t) ty ps
           Sort_gen_ax constrs isFree -> Sort_gen_ax constrs isFree
           ExtFORMULA mf -> mapMSen mapEnv vars mf
           _ -> error "Modal2CASL.transSen->mapSen"

mapMSen :: ModMapEnv -> [VAR] -> M_FORMULA -> CASLFORMULA
mapMSen mapEnv@(MME {worldSort = fws, modalityRelMap = pwRelMap}) vars f
   = let trans_f1 = mkId [mkSimpleId "Placeholder for Formula"]
         t_var = mkSimpleId "Placeholder for Modality Term"
         (w1, w2, newVars) = assert (not (null vars))
                           (let nVars =
                                 freshWorldVar vars : vars
                            in (head vars, head nVars, nVars))
         getRel mo =
              Map.findWithDefault
                    (error ("Modal2CASL: Undefined modality " ++ show mo))
                    (modalityToModName mo)
         trans' mTerm propSymb trForm nvs f1 =
             replacePropPredication mTerm
                                    propSymb (mapSen mapEnv nvs f1) trForm
         mapT = mapTERM mapEnv newVars
         vw1 = mkVarDecl w1 fws
         vw2 = mkVarDecl w2 fws
         mkPredType ts = Pred_type ts nullRange
         joinPreds b t1 t2 = if b then mkImpl t1 t2 else conjunct [t1, t2]
         quantForm b vs = if b then mkForall vs else
           mkForall (init vs) . mkExist [last vs]
         transPred = mkPredication (mkQualPred trans_f1 $ mkPredType []) []
     in
     case f of
     BoxOrDiamond b moda f1 _ ->
       let rel = getRel moda pwRelMap in
        case moda of
        Simple_mod _ -> let
          newFormula = quantForm b [vw1, vw2]
                          $ joinPreds b
                            (mkPredication
                             (mkQualPred rel $ mkPredType [fws, fws])
                             [toQualVar vw1, toQualVar vw2])
                          transPred
          in trans' Nothing trans_f1 newFormula newVars f1
        Term_mod t ->
         let tt = getModTermSort rel
             vtt = mkVarDecl t_var tt
             newFormula = quantForm b [vtt, vw1, vw2]
                          $ joinPreds b
                            (mkPredication
                             (mkQualPred rel $ mkPredType [tt, fws, fws])
                             [toQualVar vtt, toQualVar vw1, toQualVar vw2])
                          transPred
         in trans' (Just (rel, t_var, mapT t))
                                          trans_f1 newFormula
                                          newVars f1

-- head [VAR] is always the current world variable (for Application)
mapTERM :: ModMapEnv -> [VAR] -> TERM M_FORMULA -> TERM ()
mapTERM mapEnv@(MME {worldSort = fws, flexiOps = fOps}) vars t = case t of
    Qual_var v ty ps -> Qual_var v ty ps
    Application opsym as qs ->
        let as' = map (mapTERM mapEnv vars) as
            fwsTerm = sortedWorldTerm fws (head vars)
            addFws (Op_type k sorts res pps) =
                Op_type k (fws : sorts) res pps
            (opsym', as'') =
                case opsym of
                Op_name _ -> error "Modal2CASL: untyped prdication"
                Qual_op_name on opType ps ->
                    let addTup = (Qual_op_name (addPlace on)
                                               (addFws opType) ps,
                                  fwsTerm : as')
                        defTup = (opsym, as') in
                            if Set.member (toOpType opType)
                                $ MapSet.lookup on fOps
                                then addTup
                                else defTup
        in Application opsym' as'' qs
    Sorted_term trm ty ps -> Sorted_term (mapTERM mapEnv vars trm) ty ps
    Cast trm ty ps -> Cast (mapTERM mapEnv vars trm) ty ps
    Conditional t1 f t2 ps ->
       Conditional (mapTERM mapEnv vars t1)
                   (mapSen mapEnv vars f)
                   (mapTERM mapEnv vars t2) ps
    _ -> error "Modal2CASL.mapTERM"

addPlace :: Id -> Id
addPlace i@(Id ts ids ps)
    | isMixfix i = Id ((\ (x, y) -> x ++ mkSimpleId place : y)
                          (break isPlace ts)) ids ps
    | otherwise = i

modalityToModName :: MODALITY -> ModName
modalityToModName (Simple_mod sid) = SimpleM sid
modalityToModName (Term_mod t) =
    case t of
    Sorted_term _ srt _ -> SortM srt
    _ -> error ("Modal2CASL: modalityToModName: Wrong term: " ++ show t)

sortedWorldTerm :: SORT -> VAR -> TERM ()
sortedWorldTerm fws v = Sorted_term (Qual_var v fws nullRange) fws nullRange

addWorld_OP :: SORT -> OP_NAME -> Set.Set OpType
            -> Map.Map OP_NAME (Set.Set OpType)
            -> Map.Map OP_NAME (Set.Set OpType)
addWorld_OP = addWorld_ (\ ws t -> t { opArgs = ws : opArgs t})

addWorld_PRED :: SORT -> PRED_NAME -> Set.Set PredType
              -> Map.Map PRED_NAME (Set.Set PredType)
              -> Map.Map PRED_NAME (Set.Set PredType)
addWorld_PRED = addWorld_ (\ ws t -> t {predArgs = ws : predArgs t})

addWorld_ :: (Ord a) => (SORT -> a -> a)
          -> SORT -> Id -> Set.Set a
          -> Map.Map OP_NAME (Set.Set a)
          -> Map.Map OP_NAME (Set.Set a)
addWorld_ f fws k set = Map.insert (addPlace k) (Set.map (f fws) set)

freshWorldSort :: Set.Set SORT -> SORT
freshWorldSort _sorSet = mkId [mkSimpleId "g_World"]

-- List of variables for worlds
worldVars :: [SIMPLE_ID]
worldVars = map (mkSimpleId . ("g_w" ++) . show) [(1 :: Int) ..]

freshWorldVar :: [SIMPLE_ID] -> SIMPLE_ID
freshWorldVar vs = head $ filter notKnown worldVars
    where notKnown v = notElem v vs
