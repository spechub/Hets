{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./Comorphisms/ExtModal2HasCASL.hs
Copyright   :  (c) Christian Maeder, DFKI 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (MPTC-FD)
-}

module Comorphisms.ExtModal2HasCASL (ExtModal2HasCASL (..)) where

import Logic.Logic
import Logic.Comorphism

import Common.AS_Annotation
import Common.DocUtils
import Common.Id
import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.MapSet as MapSet

import Comorphisms.CASL2HasCASL

import CASL.AS_Basic_CASL as CASL
import CASL.Fold
import CASL.Morphism as CASL
import CASL.Overload
import CASL.Sign as CASL
import CASL.Sublogic as CASL
import CASL.World

import Data.List
import Data.Maybe
import Data.Function
import qualified Data.HashMap.Strict as Map
import qualified Data.Set as Set

import ExtModal.Logic_ExtModal
import ExtModal.AS_ExtModal
import ExtModal.ExtModalSign
import ExtModal.Sublogic as EM

import HasCASL.Logic_HasCASL
import HasCASL.As as HC
import HasCASL.AsUtils as HC
import HasCASL.Builtin
import HasCASL.DataAna
import HasCASL.Le as HC
import HasCASL.Unify
import HasCASL.Sublogic as HC

data ExtModal2HasCASL = ExtModal2HasCASL deriving (Show)
instance Language ExtModal2HasCASL

instance Comorphism ExtModal2HasCASL
               ExtModal ExtModalSL EM_BASIC_SPEC ExtModalFORMULA SYMB_ITEMS
               SYMB_MAP_ITEMS ExtModalSign ExtModalMorph
               CASL.Symbol CASL.RawSymbol ()
               HasCASL HC.Sublogic
               BasicSpec Sentence SymbItems SymbMapItems
               Env HC.Morphism HC.Symbol HC.RawSymbol () where
    sourceLogic ExtModal2HasCASL = ExtModal
    sourceSublogic ExtModal2HasCASL = mkTop maxSublogic
        { hasTransClos = False
        , hasFixPoints = False }
    targetLogic ExtModal2HasCASL = HasCASL
    mapSublogic ExtModal2HasCASL sl = Just HC.caslLogic
      { HC.which_logic = HOL
      , HC.has_sub = CASL.has_sub sl
      , HC.has_part = CASL.has_part sl }
    map_theory ExtModal2HasCASL (sig, allSens) = let
      (frames, sens) = partition (isFrameAx . sentence) allSens
      in case transSig sig sens of
      (mme, s) -> return
        (mme, map (\ (n, d) -> makeNamed n $ DatatypeSen [d])
           [("natural numbers", natType), ("numbered worlds", worldType)]
           ++ s ++ transFrames sig frames
              ++ map (mapNamed $ toSen sig) sens)
    has_model_expansion ExtModal2HasCASL = True
    is_weakly_amalgamable ExtModal2HasCASL = True

nomName :: Id -> Id
nomName t = Id [genToken "N"] [t] $ rangeOfId t

nomOpType :: OpType
nomOpType = mkTotOpType [] world

mkOp :: Id -> Type -> Term
mkOp i = mkOpTerm i . simpleTypeScheme

mkNomAppl :: Id -> Term
mkNomAppl pn = mkOp (nomName pn) $ trOp nomOpType

eqWorld :: Id -> Term -> Term -> Term
eqWorld i = mkEqTerm i (toType world) nr

eqW :: Term -> Term -> Term
eqW = eqWorld eqId

mkNot :: Term -> Term
mkNot = mkTerm notId notType [] nr

mkConj :: [Term] -> Term
mkConj l = (if null l then unitTerm trueId else toBinJunctor andId l) nr

mkDisj :: [Term] -> Term
mkDisj l =
  (if null l then unitTerm falseId else toBinJunctor orId l) nr

mkExQs :: [GenVarDecl] -> Term -> Term
mkExQs vs t =
  QuantifiedTerm HC.Existential vs t nr

mkExQ :: VarDecl -> Term -> Term
mkExQ vd = mkExQs [GenVarDecl vd]

mkExConj :: VarDecl -> [Term] -> Term
mkExConj vd = mkExQ vd . mkConj

tauS :: String
tauS = "tau"

tauId :: Id
tauId = genName tauS

tauCaslTy :: PredType
tauCaslTy = PredType [world, world]

tauTy :: Type
tauTy = trPrSyn $ toPRED_TYPE tauCaslTy

{- | we now consider numbered worlds:
     free type WN ::= mkWN World Nat -}
nWorldId :: SORT
nWorldId = genName "WN"

mkNWorldId :: Id
mkNWorldId = genName "mkWN"

nWorld :: Type
nWorld = toType nWorldId

binPredTy :: Type -> Type
binPredTy = getFunType unitType HC.Partial . replicate 2

isTransS :: String
isTransS = "isTrans"

isTransId :: Id
isTransId = genName isTransS

prOfBinPrTy :: Type -> Type
prOfBinPrTy = predType nr . binPredTy

prOfNwPrTy :: Type
prOfNwPrTy = prOfBinPrTy nWorld

containsS :: String
containsS = "contains"

containsId :: Id
containsId = genName containsS

transTy :: Type -> Type
transTy = getFunType unitType HC.Partial . replicate 2 . binPredTy

-- | mixfix names work for tuples and are lost after currying
trI :: Id -> Id
trI i = if isMixfix i then Id [genToken "C"] [i] $ rangeOfId i else i

trOpSyn :: OP_TYPE -> Type
trOpSyn (Op_type ok args res _) = let
  (partial, total) = case ok of
    CASL.Total -> (HC.Total, True)
    CASL.Partial -> (HC.Partial, False)
  resTy = toType res
  in if null args then if total then resTy else mkLazyType resTy
  else getFunType resTy partial $ map toType args

trOp :: OpType -> Type
trOp = trOpSyn . toOP_TYPE

trPrSyn :: PRED_TYPE -> Type
trPrSyn (Pred_type args ps) = let u = unitTypeWithRange ps in
   if null args then mkLazyType u else
   getFunType u HC.Partial $ map toType args

trPr :: PredType -> Type
trPr = trPrSyn . toPRED_TYPE

-- | add world arguments to flexible ops and preds; and add relations
transSig :: ExtModalSign -> [Named (FORMULA EM_FORMULA)]
  -> (Env, [Named Sentence])
transSig sign sens = let
    s1 = embedSign () sign
    extInf = extendedInfo sign
    flexibleOps = flexOps extInf
    flexiblePreds = flexPreds extInf
    flexOps' = addWorldOp world id flexibleOps
    flexPreds' = addWorldPred world id flexiblePreds
    rigOps' = diffOpMapSet (opMap sign) flexibleOps
    rigPreds' = diffMapSet (predMap sign) flexiblePreds
    noms = nominals extInf
    noNomsPreds = Set.fold (`MapSet.delete` nomPType) rigPreds' noms
    termMs = termMods extInf
    timeMs = timeMods extInf
    rels = Set.fold (\ m ->
      insertModPred world (Set.member m timeMs) (Set.member m termMs) m)
      MapSet.empty $ modalities extInf
    nomOps = Set.fold (\ n -> addOpTo (nomName n) nomOpType) rigOps' noms
    s2 = s1
      { sortRel = Rel.insertKey world $ sortRel sign
      , opMap = addOpMapSet flexOps' nomOps
      , predMap = addMapSet rels $ addMapSet flexPreds' noNomsPreds
      }
    env = mapSigAux trI trOp trPr (getConstructors sens) s2
    mkOpInfo t = Set.singleton . OpInfo (simpleTypeScheme t) Set.empty
    insOpInfo = Map.insertWith Set.union
    insF (i, t) = insOpInfo i . mkOpInfo t $ NoOpDefn Fun
    in ( env
         { assumps = foldr (uncurry insOpInfo)
             (foldr insF (assumps env)
             [ (tauId, tauTy)
             , (isTransId, prOfNwPrTy)
             , (reflexId, prOfNwPrTy)
             , (irreflexId, prOfNwPrTy)
             , (containsId, transTy nWorld)
             , (transId, transTy nWorld)
             , (transReflexId, transTy nWorld)
             , (transLinearOrderId, prOfNwPrTy)
             , (hasSuccessorId, hasSuccessorTy)
             , (subsetOfTauId, prOfNwPrTy)
             , (hasTauSucId, prOfNwPrTy)
             , (superpathId, hasSuccessorTy)
             , (pathId, hasSuccessorTy)
             ])
             [ altToOpInfo natId zeroAlt
             , altToOpInfo natId sucAlt
             , altToOpInfo nWorldId worldAlt
             , selWorldInfo getWorldSel
             , selWorldInfo numSel
             ]
         , typeMap = Map.insert nWorldId starTypeInfo
                       { typeDefn = DatatypeDefn worldType }
                     . Map.insert natId starTypeInfo
                       { typeDefn = DatatypeDefn natType }
                     $ typeMap env
         }
       , makeNamed "nat_induction" (Formula $ inductionScheme [natType])
         : makeDataSelEqs (toDataPat worldType) [worldAlt]
         ++ map (\ (s, t) -> makeNamed s $ Formula t)
         [ (tauS, tauDef termMs $ Set.toList timeMs)
         , (isTransS, isTransDef nWorld)
         , (reflexS, reflexDef True nWorld)
         , (irreflexS, reflexDef False nWorld)
         , (containsS, containsDef nWorld)
         , (transS, someDef transId (transContainsDef nWorld) nWorld)
         , (transReflexS, someDef transReflexId
                        (transReflexContainsDef nWorld) nWorld)
         , (transLinearOrderS, transLinearOrderDef nWorld)
         , (hasSuccessorS, hasSuccessorDef)
         , (subsetOfTauS, subsetOfTauDef)
         , (hasTauSucS, hasTauSucDefAny)
         , (superpathS, superpathDef)
         , (pathS, pathDef)
         ]
       )

vQuad :: Type -> [VarDecl]
vQuad w = map (\ n -> hcVarDecl (genNumVar "v" n) w) [1, 2, 3, 4]

quadDs :: Type -> [GenVarDecl]
quadDs = map GenVarDecl . vQuad

tripDs :: Type -> [GenVarDecl]
tripDs = take 3 . quadDs

pairDs :: Type -> [GenVarDecl]
pairDs = take 2 . tripDs

tQuad :: Type -> [Term]
tQuad = map QualVar . vQuad

tTrip :: Type -> [Term]
tTrip = take 3 . tQuad

tPair :: Type -> [Term]
tPair = take 2 . tTrip

nr :: Range
nr = nullRange

worldTy :: Type
worldTy = toType world

tauDef :: Set.Set Id -> [Id] -> Term
tauDef termMs timeMs = let ts = tPair worldTy in
         HC.mkForall (pairDs worldTy)
           . mkLogTerm eqvId nr
           (mkApplTerm (mkOp tauId tauTy) ts)
           . mkDisj
           $ map (\ tm ->
            let v = varDecl (genToken "t") tm
                term = Set.member tm termMs
            in (if term then mkExQ v else id) $ mkApplTerm
               (mkOp (relOfMod True term tm)
                . trPr $ modPredType world term tm)
               $ if term then QualVar v : ts else ts)
           timeMs

pVar :: Type -> VarDecl
pVar = hcVarDecl (genToken "P") . binPredTy

isTransDef :: Type -> Term
isTransDef w = let
  p = pVar w
  pt = QualVar p
  [t1, t2, t3] = tTrip w
  in HC.mkForall [GenVarDecl p]
         . mkLogTerm eqvId nr
             (mkApplTerm (mkOp isTransId $ prOfBinPrTy w) [pt])
             . HC.mkForall (tripDs w)
             . mkLogTerm implId nr
               (mkLogTerm andId nr
                (mkApplTerm pt [t1, t2])
                $ mkApplTerm pt [t2, t3])
             $ mkApplTerm pt [t1, t3]

trichotomyDef :: Type -> Term -> Term -> Term -> Term
trichotomyDef w pt t1 t2 = mkLogTerm orId nr
         (dichotomyDef pt t1 t2)
         $ mkEqTerm eqId w nr t1 t2

dichotomyDef :: Term -> Term -> Term -> Term
dichotomyDef pt t1 t2 = mkLogTerm orId nr
         (mkApplTerm pt [t1, t2])
         $ mkApplTerm pt [t2, t1]

linearOrderDef :: Type -> Term -> Term
linearOrderDef w pt = let
  [t1, t2, t3, t4] = tQuad w
  in HC.mkForall (pairDs w)
     . mkLogTerm implId nr
       (mkExQs (drop 2 $ quadDs w)
        . mkLogTerm andId nr
          (dichotomyDef pt t1 t3)
          $ dichotomyDef pt t2 t4)
       $ trichotomyDef w pt t1 t2

transLinearOrderS :: String
transLinearOrderS = "trans_linear_order"

transLinearOrderId :: Id
transLinearOrderId = genName transLinearOrderS

transLinearOrderDef :: Type -> Term
transLinearOrderDef w = let
  ps = rAndQ w
  [pv, qv] = map GenVarDecl ps
  ts@[pt, qt] = map QualVar ps
  in HC.mkForall [pv]
     . mkLogTerm eqvId nr
       (mkApplTerm (mkOp transLinearOrderId $ prOfBinPrTy w) [pt])
     . mkExQs [qv]
     . mkLogTerm andId nr
       (mkApplTerm (mkOp transId $ transTy w) ts)
     $ linearOrderDef w qt

natId :: SORT
natId = stringToId "Nat"

natTy :: Type
natTy = toType natId

sucId :: Id
sucId = stringToId "suc"

zero :: Id
zero = stringToId "0"

natType :: DataEntry
natType =
  DataEntry Map.empty natId Free [] rStar
  $ Set.fromList [zeroAlt, sucAlt]

zeroAlt :: AltDefn
zeroAlt = Construct (Just zero) [] HC.Total []

sucAlt :: AltDefn
sucAlt = Construct (Just sucId) [natTy] HC.Total [typeToSelector Nothing natTy]

altToTy :: Id -> AltDefn -> Type
altToTy i (Construct _ ts p _) = getFunType (toType i) p ts

altToOpInfo :: Id -> AltDefn -> (Id, Set.Set OpInfo)
altToOpInfo i c@(Construct m _ _ _) = let Just n = m in
    (n, Set.singleton .
      OpInfo (simpleTypeScheme $ altToTy i c) Set.empty
    $ ConstructData i)

getWorldId :: Id
getWorldId = genName "getWorld"

numId :: Id
numId = genName "num"

worldType :: DataEntry
worldType = DataEntry Map.empty nWorldId Free [] rStar $ Set.singleton worldAlt

worldAlt :: AltDefn
worldAlt = Construct (Just mkNWorldId) [worldTy, natTy] HC.Total
    [getWorldSel, numSel]

getWorldSel :: [Selector]
getWorldSel = typeToSelector (Just getWorldId) worldTy

numSel :: [Selector]
numSel = typeToSelector (Just numId) natTy

nWorldTy :: Type
nWorldTy = altToTy nWorldId worldAlt

selWorldInfo :: [Selector] -> (Id, Set.Set OpInfo)
selWorldInfo = selToOpInfo nWorldId . Set.singleton . ConstrInfo mkNWorldId
  $ simpleTypeScheme nWorldTy

selToTy :: Id -> [Selector] -> (Id, Type)
selToTy i s = let [Select (Just n) t p] = s in
  (n, getFunType t p [toType i])

selToOpInfo :: Id -> Set.Set ConstrInfo -> [Selector] -> (Id, Set.Set OpInfo)
selToOpInfo i c s = let (n, ty) = selToTy i s in
  (n, Set.singleton . OpInfo (simpleTypeScheme ty) Set.empty
      $ SelectData c i)

rAndQ :: Type -> [VarDecl]
rAndQ w = map (\ c -> hcVarDecl (genToken [c]) $ binPredTy w) "RQ"

containsDef :: Type -> Term
containsDef w = let -- q contains r
  ps = rAndQ w
  ts@[pt, qt] = map QualVar ps
  in HC.mkForall (map GenVarDecl ps)
     . mkLogTerm eqvId nr
       (mkApplTerm (mkOp containsId $ transTy w) ts)
     $ containsDefAux False implId pt qt w

containsDefAux :: Bool -> Id -> Term -> Term -> Type -> Term
containsDefAux neg op pt qt w = let ts = tPair w in
  HC.mkForall (pairDs w) . (if neg then mkNot else id)
     . mkLogTerm op nr (mkApplTerm pt ts) $ mkApplTerm qt ts

someContainsDef :: (Term -> Term) -> Type -> Term -> Term -> Term
someContainsDef sPred w pt qt = let -- q fulfills sPred and contains r
  ts = [pt, qt]
  in mkLogTerm andId nr (sPred qt)
       $ mkApplTerm (mkOp containsId $ transTy w) ts

transContainsDef :: Type -> Term -> Term -> Term
transContainsDef w = someContainsDef
  (\ qt -> mkApplTerm (mkOp isTransId $ prOfBinPrTy w) [qt]) w

transReflexContainsDef :: Type -> Term -> Term -> Term
transReflexContainsDef w = someContainsDef
  (\ qt -> mkLogTerm andId nr
           (mkApplTerm (mkOp isTransId $ prOfBinPrTy w) [qt])
           $ mkApplTerm (mkOp reflexId $ prOfBinPrTy w) [qt]) w

transS :: String
transS = "trans"

transId :: Id
transId = genName transS

transReflexS :: String
transReflexS = "trans_reflex"

transReflexId :: Id
transReflexId = genName transReflexS

someDef :: Id -> (Term -> Term -> Term) -> Type -> Term
someDef dId op w = let -- q is the (smallest) something containing r
  ps = rAndQ w
  ts@[pt, qt] = map QualVar ps
  z = pVar w
  zt = QualVar z
  in HC.mkForall (map GenVarDecl ps)
     . mkLogTerm eqvId nr
       (mkApplTerm (mkOp dId $ transTy w) ts)
     . mkLogTerm andId nr (op pt qt)
       . HC.mkForall [GenVarDecl z]
       . mkLogTerm implId nr (op pt zt)
         $ mkApplTerm (mkOp containsId $ transTy w) [qt, zt]

reflexS :: String
reflexS = "reflex"

irreflexS :: String
irreflexS = "irreflex"

reflexId :: Id
reflexId = genName reflexS

irreflexId :: Id
irreflexId = genName irreflexS

reflexDef :: Bool -> Type -> Term
reflexDef refl w = let
  x = hcVarDecl (genToken "x") w
  p = pVar w
  pt = QualVar p
  in HC.mkForall [GenVarDecl p]
     . mkLogTerm eqvId nr
       (mkApplTerm (mkOp (if refl then reflexId else irreflexId)
                   $ prOfBinPrTy w) [pt])
     . HC.mkForall [GenVarDecl x]
     . (if refl then id else mkNot)
     . mkApplTerm pt . replicate 2 $ QualVar x

varDecl :: Token -> SORT -> VarDecl
varDecl i = hcVarDecl i . toType

hcVarDecl :: Token -> Type -> VarDecl
hcVarDecl i t = VarDecl (simpleIdToId i) t Other nr

varTerm :: Token -> SORT -> Term
varTerm i = QualVar . varDecl i

typeToSelector :: Maybe Id -> Type -> [Selector]
typeToSelector m a = [Select m a HC.Total]

hasSuccessorS :: String
hasSuccessorS = "has_successor"

hasSuccessorId :: Id
hasSuccessorId = genName hasSuccessorS

hasSuccessorTy :: Type
hasSuccessorTy = getFunType unitType HC.Partial [worldTy, binPredTy nWorld]

tauApplTerm :: Term -> Term -> Term
tauApplTerm t1 t2 = mkApplTerm (mkOp tauId tauTy) [t1, t2]

zeroT :: Term
zeroT = mkOp zero natTy

hasSuccessorDef :: Term
hasSuccessorDef = let
  [x0, p] = xZeroAndP
  (tT, _, rT) = hasTauSucDefAux zeroT
  in HC.mkForall (map GenVarDecl [x0, p])
     . mkLogTerm eqvId nr
       (mkApplTerm (mkOp hasSuccessorId hasSuccessorTy) $ map QualVar [x0, p])
     $ mkLogTerm implId nr tT rT

xZeroAndP :: [VarDecl]
xZeroAndP = [hcVarDecl (genNumVar "x" 0) worldTy, pVar nWorld]

pairWorld :: Term -> Term -> Term
pairWorld t1 t2 = mkApplTerm (mkOp mkNWorldId nWorldTy) [t1, t2]

sucTy :: Type
sucTy = altToTy natId sucAlt

sucTerm :: Term -> Term
sucTerm t = mkApplTerm (mkOp sucId sucTy) [t]

hasTauSucDefAux :: Term -> (Term, Term, Term)
hasTauSucDefAux nT = let
  x = hcVarDecl (genToken "x") worldTy
  vs = xZeroAndP
  [xt, xt0, pt] = map QualVar $ x : vs
  tauAppl = tauApplTerm xt0 xt
  pw = pairWorld xt0 nT
  in (mkExQ x tauAppl, pw,
     mkExQ x
     . mkLogTerm andId nr tauAppl
     $ mkApplTerm pt [pw, pairWorld xt $ sucTerm nT])

hasTauSucS :: String
hasTauSucS = "has_tau_suc"

hasTauSucId :: Id
hasTauSucId = genName hasTauSucS

hasTauSucDefAny :: Term
hasTauSucDefAny = let
  nv = hcVarDecl (genToken "n") natTy
  nt = QualVar nv
  [x0, p] = xZeroAndP
  (tT, pw, rT) = hasTauSucDefAux nt
  y = hcVarDecl (genToken "y") nWorld
  in HC.mkForall [GenVarDecl p]
     . mkLogTerm eqvId nr
       (mkApplTerm (mkOp hasTauSucId prOfNwPrTy) [QualVar p])
     . HC.mkForall (map GenVarDecl [x0, nv])
     $ mkLogTerm implId nr
       (mkLogTerm andId nr
        (mkExQ y $ mkApplTerm (QualVar p) [QualVar y, pw])
        tT) rT

subsetOfTauS :: String
subsetOfTauS = "subset_of_tau"

subsetOfTauId :: Id
subsetOfTauId = genName subsetOfTauS

getWorld :: Term -> Term
getWorld t = mkApplTerm (uncurry mkOp $ selToTy nWorldId getWorldSel) [t]

subsetOfTauDef :: Term
subsetOfTauDef = let
  p = pVar nWorld
  pt = QualVar p
  ts@[xt, yt] = tPair nWorld
  in HC.mkForall [GenVarDecl p]
     . mkLogTerm eqvId nr
       (mkApplTerm (mkOp subsetOfTauId prOfNwPrTy) [pt])
     . HC.mkForall (pairDs nWorld)
     . mkLogTerm implId nr
       (mkApplTerm pt ts)
     . tauApplTerm (getWorld xt) $ getWorld yt

superpathS :: String
superpathS = "superpath"

superpathId :: Id
superpathId = genName superpathS

superpathDef :: Term
superpathDef = let
  vs = xZeroAndP
  ts@[_, pt] = map QualVar vs
  in HC.mkForall (map GenVarDecl vs)
     . mkLogTerm eqvId nr
       (mkApplTerm (mkOp superpathId hasSuccessorTy) ts)
     . mkConj
     $ mkApplTerm (mkOp hasSuccessorId hasSuccessorTy) ts
      : map (\ i -> mkApplTerm (mkOp i prOfNwPrTy) [pt])
        [irreflexId, subsetOfTauId, hasTauSucId, transLinearOrderId]

pathS :: String
pathS = "path"

pathId :: Id
pathId = genName pathS

pathAppl :: [Term] -> Term
pathAppl = mkApplTerm $ mkOp pathId hasSuccessorTy

pathDef :: Term
pathDef = let
  vs = xZeroAndP
  [rv, qv] = rAndQ nWorld
  [rt, qt] = map QualVar [rv, qv]
  ts@[x0, pt] = map QualVar vs
  in HC.mkForall (map GenVarDecl vs)
     . mkLogTerm eqvId nr
       (pathAppl ts)
     . mkExQ rv
     $ mkConj
       [ mkApplTerm (mkOp superpathId hasSuccessorTy) [x0, rt]
       , mkApplTerm (mkOp transReflexId $ transTy nWorld) [rt, pt]
       , HC.mkForall [GenVarDecl qv]
         . mkLogTerm implId nr
           (mkApplTerm (mkOp superpathId hasSuccessorTy) [x0, qt])
         . mkLogTerm orId nr
           (containsDefAux True implId qt rt nWorld)
           $ containsDefAux False eqvId qt rt nWorld
       ]

toSen :: ExtModalSign -> FORMULA EM_FORMULA -> Sentence
toSen msig f = case f of
   Sort_gen_ax cs b -> let
       (sorts, ops, smap) = recover_Sort_gen_ax cs
       genKind = if b then Free else Generated
       mapPart :: OpKind -> Partiality
       mapPart cp = case cp of
                CASL.Total -> HC.Total
                CASL.Partial -> HC.Partial
       in DatatypeSen $ map ( \ s ->
          DataEntry (Map.fromList smap) s genKind [] rStar
          $ Set.fromList $ map ( \ (i, t) ->
            let args = map toType $ opArgs t in
            Construct (if isInjName i then Nothing else Just i) args
              (mapPart $ opKind t)
              $ map (typeToSelector Nothing) args)
          $ filter ( \ (_, t) -> opRes t == s)
                $ map ( \ o -> case o of
                        Qual_op_name i t _ -> (trI i, toOpType t)
                        _ -> error "ExtModal2HasCASL.toSentence") ops) sorts
   _ -> Formula $ transTop msig f

transFrames :: ExtModalSign -> [Named (FORMULA EM_FORMULA)] -> [Named Sentence]
transFrames sig = foldr (\ nf -> case sentence nf of
  ExtFORMULA (ModForm (ModDefn _ _ _ fs _)) ->
     (map (\ af -> let l = getRLabel af in
           nf { sentence = Formula $ transTop sig (item af)
              , senAttr = if null l then senAttr nf else l })
     (concatMap (frameForms . item) fs) ++)
  _ -> id) []

isFrameAx :: FORMULA EM_FORMULA -> Bool
isFrameAx f = case f of
  ExtFORMULA (ModForm _) -> True
  _ -> False

data Args = Args
  { sourceW, targetW, targetN :: Term
  , nextW, freeC :: Int  -- world variables
  , freeZ :: Int -- path variable
  , boundNoms :: [(Id, Term)]
  , modSig :: ExtModalSign
  }

startArgs :: ExtModalSign -> Args
startArgs msig = let
  vt = varTerm (genNumVar "w" 1) world
  in Args
  { sourceW = vt
  , targetW = vt
  , targetN = zeroT
  , nextW = 1
  , freeC = 1
  , freeZ = 1
  , boundNoms = []
  , modSig = msig
  }

zDecl :: Args -> VarDecl
zDecl as = hcVarDecl (genNumVar "Z" $ freeZ as) $ binPredTy nWorld

transTop :: ExtModalSign -> FORMULA EM_FORMULA -> Term
transTop msig f = let
  as = startArgs msig
  vs = [hcVarDecl (genNumVar "w" 1) worldTy, zDecl as]
  in HC.mkForall (map GenVarDecl vs)
     . mkLogTerm implId nr
     (pathAppl $ map QualVar vs)
     $ transMF as f

getTermOfNom :: Args -> Id -> Term
getTermOfNom as i = fromMaybe (mkNomAppl i) . lookup i $ boundNoms as

mkZPath :: Term -> Term -> Args -> Term
mkZPath v n as = mkApplTerm (QualVar $ zDecl as)
    [pairWorld v n, pairWorld (targetW as) $ targetN as]

zPath :: Args -> Term
zPath as = mkZPath (sourceW as) zeroT as

trRecord :: Args -> String -> Record EM_FORMULA Term Term
trRecord as str = let
    extInf = extendedInfo $ modSig as
    currW = targetW as
    andPath = mkLogTerm andId nr $ zPath as
    typeTerm hty tr = case getTypeOf tr of
      Just t | hty == t -> tr
      _ -> TypedTerm tr Inferred hty nr
    typeArgs = zipWith (typeTerm . toType)
    in (transRecord str)
  { foldPredication = \ _ ps pargs _ -> let
      Qual_pred_name pn pTy@(Pred_type srts q) _ = ps
      args = typeArgs srts pargs
      in andPath
         $ typeTerm unitType
         $ if MapSet.member pn (toPredType pTy) $ flexPreds extInf
         then mkApplTerm
            (mkOp (trI pn) . trPrSyn
            $ Pred_type (world : srts) q) $ currW : args
         else if null srts && Set.member pn (nominals extInf)
              then eqW currW $ getTermOfNom as pn
         else mkApplTerm
            (mkOp (trI pn) $ trPrSyn pTy) args
  , foldEquation = \ o t1 e t2 ps ->
        let Equation c1 _ _ _ = o in
        andPath $ mkEqTerm (if e == Existl then exEq else eqId)
                     (typeOfTerm c1) ps t1 t2
  , foldDefinedness = \ o t ps ->
        let Definedness c _ = o in
        andPath $ mkTerm defId defType [typeOfTerm c] ps t
  , foldExtFORMULA = \ _ f -> transEMF as f
  , foldApplication = \ _ os oargs _ -> let
      Qual_op_name opn oTy@(Op_type ok srts res q) _ = os
      args = typeArgs srts oargs
      in typeTerm (toType res)
         $ if MapSet.member opn (toOpType oTy) $ flexOps extInf
         then mkApplTerm
            (mkOp (trI opn) . trOpSyn
            $ Op_type ok (world : srts) res q) $ currW : args
         else mkApplTerm
            (mkOp (trI opn) $ trOpSyn oTy) args
  }

transMF :: Args -> FORMULA EM_FORMULA -> Term
transMF a f = foldFormula (trRecord a $ showDoc f "") f

disjointVars :: [VarDecl] -> [Term]
disjointVars vs = case vs of
  a : r@(b : _) -> mkNot
    (on eqW QualVar a b) : disjointVars r
  _ -> []

pathAppl2 :: Term -> VarDecl -> Term
pathAppl2 t v = pathAppl [t, QualVar v]

transEMF :: Args -> EM_FORMULA -> Term
transEMF as emf = let
  fW = freeC as
  pathAppl3 t = mkLogTerm implId nr . pathAppl2 t
  is i = [fW + 1 .. fW + i]
  mkVs c ty = map (\ n -> varDecl (genNumVar [c] n) ty) . is
  vds = mkVs 'w' world
  nds = mkVs 'n' natId
  gvs = map GenVarDecl . vds
  vt0 = targetW as
  nt0 = targetN as
  [v1] = vds 1
  [n1] = nds 1
  [vt1, nt1] = map QualVar [v1, n1]
  gvs1 = map GenVarDecl [v1, n1]
  mkEqNats = mkEqTerm eqId natTy nr
  in case emf of
  PrefixForm pf f r -> case pf of
    BoxOrDiamond bOp m gEq i -> let
      ex = bOp == Diamond
      l = is i
      gs = gvs i
      nAs = as { freeC = fW + i }
      tf n = let
        vt = varTerm (genNumVar "w" n) world
        newAs = nAs { freeZ = n }
        zd = zDecl newAs
        in HC.mkForall [GenVarDecl zd]
           . pathAppl3 vt zd
            $ transMF (resetArgs vt newAs) f
      tM n = transMod nAs { nextW = n } m
      conjF = mkConj $ map tM l ++ map tf l ++ disjointVars (vds i)
      diam = BoxOrDiamond Diamond m True
      tr b = transEMF as $ PrefixForm (BoxOrDiamond b m gEq i) f r
      f1 = QuantifiedTerm HC.Existential gs conjF r
      f2 = HC.mkForall gs conjF
      in if gEq && i > 0 && (i == 1 || ex) then case bOp of
           Diamond -> f1
           Box -> f2
           EBox -> mkConj [f1, f2]
         else if i <= 0 && ex && gEq then unitTerm trueId r
         else if bOp == EBox then mkConj $ map tr [Diamond, Box]
         else if ex -- lEq
              then transMF as . mkNeg . ExtFORMULA $ PrefixForm
                       (diam $ i + 1) f r
         else if gEq -- Box
              then transMF as . mkNeg . ExtFORMULA $ PrefixForm
                       (diam i) (mkNeg f) r
              else transMF as . ExtFORMULA $ PrefixForm
                       (diam $ i + 1) (mkNeg f) r
    Hybrid at i -> let ni = simpleIdToId i in
      if at then let
           ti = getTermOfNom as ni
           nAs = as { freeC = fW + 1, freeZ = fW + 1 }
           zd = zDecl nAs
           in mkConj
           [ zPath as, HC.mkForall [GenVarDecl zd]
           . pathAppl3 ti zd $ transMF (resetArgs ti as) f ]
      else let
      vi = varDecl (genNumVar "i" $ fW + 1) world
      ti = QualVar vi
      in mkExConj vi
           [ eqW ti vt0
           , transMF as { boundNoms = (ni, ti) : boundNoms as
                        , targetW = ti
                        , freeC = fW + 1 } f ]
    StateQuantification fut gen -> let
      nAs = as { freeC = fW + 1, targetW = vt1, targetN = nt1 }
      in mkLogTerm andId r (zPath as)
         . (if gen then HC.mkForall else mkExQs) gvs1
         . mkLogTerm (if gen then implId else andId) nr
           (if fut then mkZPath vt0 nt0 nAs else mkZPath vt1 nt1 as)
           $ transMF nAs f
    PathQuantification gen -> if gen then let
      ws = mkVs 'p' nWorldId 2
      [w1, w2] = map QualVar ws
      p = pairWorld vt0 nt0
      nAs = as { freeC = fW + 2, freeZ = fW + 1 }
      zd = zDecl nAs
      zt = QualVar zd
      z = QualVar $ zDecl as
      in mkLogTerm andId r (zPath as)
         . HC.mkForall [GenVarDecl zd]
         . mkLogTerm implId r
           (mkLogTerm andId r (pathAppl2 (sourceW as) zd)
            . HC.mkForall gvs1
            . mkLogTerm andId r
              (mkLogTerm eqvId r
               (mkZPath vt1 nt1 as) $ mkZPath vt1 nt1 nAs)
            . HC.mkForall (map GenVarDecl ws)
            . mkLogTerm implId r
              (mkLogTerm andId r
               (mkApplTerm z [w1, p])
               $ mkApplTerm z [w2, p])
            . mkLogTerm eqvId r
              (mkApplTerm z [w1, w2])
              $ mkApplTerm zt [w1, w2])
         $ transMF nAs f
      else transMF as . mkNeg . ExtFORMULA $ PrefixForm
               (PathQuantification $ not gen) (mkNeg f) r
    NextY next -> let
      nAs = as { freeC = fW + 1, targetW = vt1 }
      in mkLogTerm andId r (zPath as)
         . mkExQs (if next then [GenVarDecl v1] else gvs1)
         $ if next then let
               as2 = nAs { targetN = sucTerm nt0 }
               in mkLogTerm andId r (mkZPath vt0 nt0 as2)
                  $ transMF as2 f
           else let
               as2 = nAs { targetN = nt1 }
               in mkConj
               [ mkZPath vt1 nt1 as
               , mkEqNats (sucTerm nt1) nt0
               , transMF as2 f ]
    FixedPoint _ _ -> error $ "transEMF: " ++ showDoc emf ""
  UntilSince isUntil f1 f2 r -> let
    nAs = as { freeC = fW + 2 }
    [_, v2] = vds 2
    [_, n2] = nds 2
    [vt2, nt2] = map QualVar [v2, n2]
    as1 = nAs { targetW = vt1, targetN = nt1 }
    as2 = nAs { targetW = vt2, targetN = nt2 }
    in mkLogTerm andId r (zPath as)
      . mkExQs (map GenVarDecl [v1, n1])
      $ mkConj
      [ if isUntil then mkZPath vt0 nt0 as1 else mkZPath vt1 nt1 as
      , transMF as1 f2
      , HC.mkForall (map GenVarDecl [v2, n2])
        . mkLogTerm orId r
        (mkConj
        [ mkLogTerm orId r
          (if isUntil then mkZPath vt0 nt0 as2 else mkZPath vt2 nt2 as)
          . mkLogTerm andId r (eqW vt0 vt2)
          $ mkEqNats nt0 nt2
        , if isUntil then mkZPath vt2 nt2 as1 else mkZPath vt1 nt1 as2 ])
        $ transMF as2 f1 ]
  ModForm md -> mkConj $ transModDefn as md

resetArgs :: Term -> Args -> Args
resetArgs t as = as
  { sourceW = t
  , targetW = t
  , targetN = zeroT }

transMod :: Args -> MODALITY -> Term
transMod as md = let
  t1 = targetW as
  t2 = varTerm (genNumVar "w" $ nextW as) world
  vts = [t1, t2]
  msig = modSig as
  extInf = extendedInfo msig
  timeMs = timeMods extInf
  in case md of
  SimpleMod i -> let ri = simpleIdToId i in mkApplTerm
    (mkOp (relOfMod (Set.member ri timeMs) False ri)
                    . trPr $ modPredType world False ri) vts
  TermMod t -> case optTermSort t of
    Just srt -> case keepMinimals msig id . Set.toList
      . Set.intersection (termMods extInf) . Set.insert srt
      $ supersortsOf srt msig of
      [] -> error $ "transMod1: " ++ showDoc t ""
      st : _ -> mkApplTerm
        (mkOp (relOfMod (Set.member st timeMs) True st)
         . trPr $ modPredType world True st)
        $ foldTerm (trRecord (resetArgs t1 as) $ showDoc t "") t : vts
    _ -> error $ "transMod2: " ++ showDoc t ""
  Guard f -> let
    nf = freeC as + 1
    newAs = as { freeC = nf, freeZ = nf }
    zd = zDecl newAs
    in mkConj [eqWorld exEq t1 t2, HC.mkForall [GenVarDecl zd] $ mkConj
         [ pathAppl2 t1 zd, transMF (resetArgs t1 newAs) f ]]
  ModOp mOp m1 m2 -> case mOp of
    Composition -> let
      nW = freeC as + 1
      nAs = as { freeC = nW }
      vd = varDecl (genNumVar "w" nW) world
      in mkExConj vd
           [ transMod nAs { nextW = nW } m1
           , transMod nAs { targetW = QualVar vd } m2 ]
    Intersection -> mkConj [transMod as m1, transMod as m2]
    Union -> mkDisj [transMod as m1, transMod as m2]
    OrElse -> mkDisj $ transOrElse [] as $ flatOrElse md
  TransClos m -> transMod as m -- ignore transitivity for now

flatOrElse :: MODALITY -> [MODALITY]
flatOrElse md = case md of
  ModOp OrElse m1 m2 -> flatOrElse m1 ++ flatOrElse m2
  _ -> [md]

transOrElse :: [FORMULA EM_FORMULA] -> Args -> [MODALITY] -> [Term]
transOrElse nFs as ms = case ms of
  [] -> []
  md : r -> case md of
    Guard f -> transMod as (Guard . conjunct $ f : nFs)
      : transOrElse (mkNeg f : nFs) as r
    _ -> transMod as md : transOrElse nFs as r

transModDefn :: Args -> ModDefn -> [Term]
transModDefn as (ModDefn _ _ _ fs _) =
  concatMap (map (transMF as . item) . frameForms . item) fs
