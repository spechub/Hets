{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich and Uni Bremen 2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The possible world encoding comorphism from ModalCASL to CASL.

   We use the Relational Translation by adding one extra parameter of
   type world to each predicate.

-}

module Comorphisms.Modal2CASL (Modal2CASL(..)) where

import Logic.Logic
import Logic.Comorphism
import qualified Data.Set as Set
import qualified Data.Map as Map
import Common.AS_Annotation
import Common.Id

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

import Data.Maybe
-- Debugging
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
               Symbol RawSymbol Q_ProofTree where
    sourceLogic Modal2CASL = Modal
    sourceSublogic Modal2CASL = ()
    targetLogic Modal2CASL = CASL
    mapSublogic Modal2CASL _ = Just SL.caslTop
    map_theory (Modal2CASL) (sig, sens) = case transSig sig of
      mme -> return (caslSign mme, relFormulas mme
                     ++ map (mapNamed $ transSen sig) sens)
    map_morphism Modal2CASL = return . mapMor
    map_sentence Modal2CASL sig = return . transSen sig
    map_symbol Modal2CASL = Set.singleton . mapSym
    has_model_expansion Modal2CASL = True
    is_weakly_amalgamable Modal2CASL = True

data ModName = SimpleM SIMPLE_ID
             | SortM   SORT
               deriving (Show,Ord,Eq)

type ModalityRelMap = Map.Map ModName PRED_NAME
data ModMapEnv = MME { caslSign :: CASLSign,
                       worldSort :: SORT,
                       modalityRelMap :: ModalityRelMap,
                       flexOps :: Map.Map OP_NAME (Set.Set OpType),
--                     rigOps :: Map.Map OP_NAME (Set.Set OpType),
                       flexPreds :: Map.Map PRED_NAME (Set.Set PredType),
--                     rigPreds :: Map.Map PRED_NAME (Set.Set PredType),
                       relFormulas :: [Named CASLFORMULA]
                     }

--  (CASL signature,World sort introduced,[introduced relations on possible worlds],)


transSig :: MSign -> ModMapEnv
transSig sign =
 {-   trace ("Flexible Ops: " ++ show flexibleOps ++
           "\nRigid Ops: "  ++ show rigOps' ++
           "\nOriginal Ops: " ++ show (opMap sign) ++ "\n" ++
           "Flexible Preds: " ++ show flexiblePreds ++
           "\nRigid Preds: "  ++ show rigPreds' ++
           "\nOriginal Preds: " ++ show (predMap sign) ++ "\n"
          )  -}
   let sorSet     = sortSet sign
       fws        = freshWorldSort sorSet
       flexOps'   = Map.foldWithKey (addWorld_OP fws)
                                    Map.empty $ flexibleOps
       flexPreds' = addWorldRels True relsTermMod $
                    addWorldRels False relsMod $
                    Map.foldWithKey (addWorld_PRED fws)
                                    Map.empty $ flexiblePreds
       rigOps'    = rigidOps $ extendedInfo sign
       rigPreds'  = rigidPreds $ extendedInfo sign
       flexibleOps   = diffMapSet (opMap sign) rigOps'
       flexiblePreds = diffMapSet (predMap sign) rigPreds'
       relations = Map.union relsMod relsTermMod
       genRels f mp = Map.foldWithKey (\me _ nm -> f me nm) Map.empty mp
       genModFrms f mp = Map.foldWithKey f [] mp
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
                             then [getModTermSort rs,fws,fws]
                             else [fws,fws] in
               Map.fold (\rs nm -> Map.insert rs
                                              (Set.singleton $
                                                    PredType $ argSorts rs)
                                              nm)
                        mp rels
       partMME = MME {caslSign =
            (emptySign ())
               {sortSet = Set.insert fws sorSet
               , sortRel = sortRel sign
               , opMap = Map.unionWith Set.union flexOps' rigOps'
               , assocOps = diffMapSet (assocOps sign) flexibleOps
               , predMap = Map.unionWith Set.union flexPreds' rigPreds'},
         worldSort = fws,
         modalityRelMap = relations,
         flexOps = flexibleOps,
--       rigOps = rigOps',
         flexPreds = flexiblePreds,
--       rigPreds = rigPreds',
         relFormulas = []}
      in partMME { relFormulas = relModFrms++relTermModFrms}

{- ModalSign { rigidOps :: Map.Map Id (Set.Set OpType)
   , rigidPreds :: Map.Map Id (Set.Set PredType)
   , modies :: Set.Set SIMPLE_ID
   , termModies :: Set.Set Id --SORT
                              }

-}

mapMor :: ModalMor -> CASLMor
mapMor m = (embedMorphism ()
    (caslSign $ transSig $ msource m)
    $ caslSign $ transSig $ mtarget m)
  { sort_map = sort_map m
  , fun_map = fun_map m
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
mapSenTop mapEnv@(MME{worldSort = fws}) f =
    case f of
    Quantification q@(Universal) vs frm ps ->
        Quantification q (qwv:vs) (mapSen mapEnv wvs frm) ps
    f1 -> Quantification Universal [qwv] (mapSen mapEnv wvs f1) nullRange
    where qwv = Var_decl wvs fws nullRange
          wvs = [head worldVars]


-- head [VAR] is always the current world variable (for predication)
mapSen :: ModMapEnv -> [VAR] -> ModalFORMULA -> CASLFORMULA
mapSen mapEnv@(MME{worldSort = fws,flexPreds=fPreds}) vars
       f = case f of
           Quantification q vs frm ps ->
                  Quantification q vs (mapSen mapEnv vars frm) ps
           Conjunction fs ps ->
               Conjunction (map (mapSen mapEnv vars) fs) ps
           Disjunction fs ps ->
               Disjunction (map (mapSen mapEnv vars) fs) ps
           Implication f1 f2 b ps ->
               Implication (mapSen mapEnv vars f1) (mapSen mapEnv vars f2) b ps
           Equivalence f1 f2 ps ->
               Equivalence (mapSen mapEnv vars f1) (mapSen mapEnv vars f2) ps
           Negation frm ps -> Negation (mapSen mapEnv vars frm) ps
           True_atom ps -> True_atom ps
           False_atom ps -> False_atom ps
           Existl_equation t1 t2 ps ->
               Existl_equation (mapTERM mapEnv vars t1) (mapTERM mapEnv vars t2) ps
           Strong_equation t1 t2 ps ->
                  Strong_equation (mapTERM mapEnv vars t1) (mapTERM mapEnv vars t2) ps
           Predication pn as qs ->
               let as'        = map (mapTERM mapEnv vars) as
                   fwsTerm    = sortedWorldTerm fws (head vars)
                   (pn',as'') =
                       case pn of
                       Pred_name _ -> error "Modal2CASL: untyped predication"
                       Qual_pred_name prn pType@(Pred_type sorts pps) ps ->
                         let addTup = (Qual_pred_name (addPlace prn)
                                             (Pred_type (fws:sorts) pps) ps,
                                       fwsTerm:as')
                             defTup = (pn,as') in
                          maybe defTup
                            (\ ts -> assert (not $ Set.null ts)
                                 (if Set.member (toPredType pType) ts
                                     then addTup
                                     else defTup))
                            (Map.lookup prn fPreds)
               in Predication pn' as'' qs
           Definedness t ps -> Definedness (mapTERM mapEnv vars t) ps
           Membership t ty ps -> Membership (mapTERM mapEnv vars t) ty ps
           Sort_gen_ax constrs isFree -> Sort_gen_ax constrs isFree
           ExtFORMULA mf -> mapMSen mapEnv vars mf
           _ -> error "Modal2CASL.transSen->mapSen"

mapMSen :: ModMapEnv -> [VAR] -> M_FORMULA -> CASLFORMULA
mapMSen mapEnv@(MME{worldSort=fws,modalityRelMap=pwRelMap}) vars f
   = let trans_f1 = mkId [mkSimpleId "Placeholder for Formula"]
         t_var    = mkSimpleId "Placeholder for Modality Term"
         (w1,w2,newVars) = assert (not (null vars))
                           (let nVars =
                                 freshWorldVar (vars) : vars
                            in (head vars, head nVars, nVars))
         getRel mo map' =
              Map.findWithDefault
                    (error ("Modal2CASL: Undefined modality " ++ show mo))
                    (modalityToModName mo)
                    map'
         trans' mTerm propSymb trForm nvs f1 =
             replacePropPredication mTerm
                                    propSymb (mapSen mapEnv nvs f1) trForm
         mapT = mapTERM mapEnv newVars
     in
     case f of
     BoxOrDiamond True moda f1 _ ->
       let rel = getRel moda pwRelMap in
        case moda of
        Simple_mod _ ->
          case map sentence
               $  concat [inlineAxioms CASL
                       " sort fws \n\
                       \ pred rel : fws * fws; \n\
                       \      trans_f1 : () \n\
                       \ vars w1 : fws \n\
                       \ . forall w2 : fws . rel(w1,w2) => \n\
                       \      trans_f1"] of
                   [newFormula] -> trans' Nothing
                                          trans_f1 newFormula newVars f1
                   _  -> error "Modal2CASL: mapMSen: impossible error"
        Term_mod t ->
         let tt    = getModTermSort rel in
          case map sentence
               $  concat [inlineAxioms CASL
                       " sort fws,tt \n\
                       \ pred rel : tt * fws * fws; \n\
                       \      trans_f1 : () \n\
                       \ vars w1 : fws; t_var : tt \n\
                       \ . forall w2 : fws . rel(t_var,w1,w2) => \n\
                       \      trans_f1"] of
                   [newFormula] -> trans' (Just (rel,t_var,mapT t))
                                          trans_f1 newFormula
                                          newVars f1
                   _  -> error "Modal2CASL: mapMSen: impossible error"

     BoxOrDiamond False moda f1 _ ->
       let rel = getRel moda pwRelMap in
        case moda of
        Simple_mod _ ->
          case map sentence
               $  concat [inlineAxioms CASL
                       " sort fws \n\
                       \ pred rel : fws * fws; \n\
                       \      trans_f1 : () \n\
                       \ vars w1 : fws \n\
                       \ . exists w2 : fws . rel(w1,w2) /\\ \n\
                       \      trans_f1"] of
                   [newFormula] -> trans' Nothing
                                          trans_f1 newFormula newVars f1
                   _  -> error "Modal2CASL: mapMSen: impossible error"
        Term_mod t ->
         let tt = getModTermSort rel in
          case map sentence
               $  concat [inlineAxioms CASL
                       " sort fws,tt \n\
                       \ pred rel : tt * fws * fws; \n\
                       \      trans_f1 : () \n\
                       \ vars w1 : fws; t_var:tt \n\
                       \ . exists w2 : fws . rel(t_var,w1,w2) /\\ \n\
                       \      trans_f1"] of
                   [newFormula] -> trans' (Just (rel,t_var,mapT t))
                                          trans_f1 newFormula newVars f1
                   _  -> error "Modal2CASL: mapMSen: impossible error"

-- head [VAR] is always the current world variable (for Application)
mapTERM :: ModMapEnv -> [VAR] -> TERM M_FORMULA -> TERM ()
mapTERM mapEnv@(MME{worldSort=fws,flexOps=fOps}) vars t = case t of
    Qual_var v ty ps -> Qual_var v ty ps
    Application opsym as qs  ->
        let as'        = map (mapTERM mapEnv vars) as
            fwsTerm    = sortedWorldTerm fws (head vars)
            addFws (Op_type k sorts res pps) =
                Op_type k (fws:sorts) res pps
            (opsym',as'') =
                case opsym of
                Op_name _ -> error "Modal2CASL: untyped prdication"
                Qual_op_name on opType ps ->
                    let addTup = (Qual_op_name (addPlace on)
                                               (addFws opType) ps,
                                  fwsTerm:as')
                        defTup = (opsym,as') in
                    maybe defTup
                          (\ ts -> assert (not $ Set.null ts)
                            (if Set.member (toOpType opType) ts
                                then addTup
                                else defTup))
                          (Map.lookup on fOps)
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
    | isMixfix i = Id ((\ (x,y) -> x++mkSimpleId place:y)
                          (span (not . isPlace) ts)) ids ps
    | otherwise  = i

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
addWorld_OP = addWorld_ (\ws t -> t { opArgs = ws : opArgs t})

addWorld_PRED :: SORT -> PRED_NAME -> Set.Set PredType
              -> Map.Map PRED_NAME (Set.Set PredType)
              -> Map.Map PRED_NAME (Set.Set PredType)
addWorld_PRED = addWorld_ (\ws t -> t {predArgs = ws : predArgs t})

addWorld_ :: (Ord a) => (SORT -> a -> a)
          -> SORT -> Id -> Set.Set a
          -> Map.Map OP_NAME (Set.Set a)
          -> Map.Map OP_NAME (Set.Set a)
addWorld_ f fws k set mp = Map.insert (addPlace k) (Set.map (f fws) set) mp

{-
-- List of sort ids for possible Worlds
worldSorts :: [SORT]
worldSorts = map mkSORT ("World":map (\x -> "World" ++ show x) [(1::Int)..])
    where mkSORT s = mkId [mkSimpleId s]
-}

freshWorldSort :: Set.Set SORT -> SORT
freshWorldSort _sorSet = mkId [mkSimpleId "g_World"]
    -- head . filter notKnown worldSorts
    -- where notKnown s = not $ s `Set.member` sorSet

-- List of variables for worlds
worldVars :: [SIMPLE_ID]
worldVars = map mkSimpleId $ map (\ x -> "g_w" ++ show x) [(1::Int)..]

freshWorldVar :: [SIMPLE_ID] -> SIMPLE_ID
freshWorldVar vs = head . (filter notKnown) $ worldVars
    where notKnown v = not $ elem v vs


{-
-- construct a relation from a given modality symbol which is new
consRelation :: Pred_map -- ^ map of allready known predicate symbols
             ->
-}
