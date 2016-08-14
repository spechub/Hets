{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./OWL2/CASL2OWL.hs
Description :  Comorphism from CASL to OWL2
Copyright   :  (c) C. Maeder, DFKI GmbH 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (via Logic.Logic)
-}

module OWL2.CASL2OWL where

import Logic.Logic as Logic
import Logic.Comorphism

import Common.AS_Annotation
import Common.DocUtils
import Common.Result
import Common.Id
import Common.ProofTree
import Common.Utils
import qualified Common.Lib.MapSet as MapSet

import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.List
import Data.Maybe

-- OWL = codomain
import OWL2.Logic_OWL2
import OWL2.MS
import OWL2.AS
import OWL2.ProfilesAndSublogics
import OWL2.ManchesterPrint ()
import OWL2.Morphism
import OWL2.Symbols
import OWL2.Sign as OS
import OWL2.Translate

-- CASL = domain
import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.Disambiguate
import CASL.Sign as CS
import qualified CASL.MapSentence as MapSen
import CASL.Morphism
import CASL.SimplifySen
import CASL.Sublogic
import CASL.ToDoc
import CASL.Overload

data CASL2OWL = CASL2OWL deriving Show

instance Language CASL2OWL

instance Comorphism
    CASL2OWL        -- comorphism
    CASL            -- lid domain
    CASL_Sublogics  -- sublogics domain
    CASLBasicSpec   -- Basic spec domain
    CASLFORMULA     -- sentence domain
    SYMB_ITEMS      -- symbol items domain
    SYMB_MAP_ITEMS  -- symbol map items domain
    CASLSign        -- signature domain
    CASLMor         -- morphism domain
    Symbol          -- symbol domain
    RawSymbol       -- rawsymbol domain
    ProofTree       -- proof tree domain
    OWL2            -- lid codomain
    ProfSub         -- sublogics codomain
    OntologyDocument -- Basic spec codomain
    Axiom           -- sentence codomain
    SymbItems       -- symbol items codomain
    SymbMapItems    -- symbol map items codomain
    OS.Sign         -- signature codomain
    OWLMorphism     -- morphism codomain
    Entity          -- symbol codomain
    RawSymb         -- rawsymbol codomain
    ProofTree       -- proof tree codomain
    where
      sourceLogic CASL2OWL = CASL
      sourceSublogic CASL2OWL = caslTop
        { sub_features = LocFilSub }
      targetLogic CASL2OWL = OWL2
      mapSublogic CASL2OWL _ = Just topS
      map_theory CASL2OWL = mapTheory

{- names must be disambiguated as is done in CASL.Qualify or SuleCFOL2SoftFOL.
   Ops or preds in the overload relation denote the same objectProperty!
-}

toC :: Id -> ClassExpression
toC = Expression . idToIRI

toO :: Id -> Int -> ObjectPropertyExpression
toO i = ObjectProp . idToNumberedIRI i

toACE :: Id -> (Annotations, ClassExpression)
toACE i = ([], toC i)

toEBit :: Id -> ListFrameBit
toEBit i = ExpressionBit [toACE i]

mkDR :: DomainOrRange -> Id -> FrameBit
mkDR dr = ListFrameBit (Just $ DRRelation dr) . toEBit

mkObjEnt :: String -> Id -> Int -> String -> FrameBit -> Named Axiom
mkObjEnt s i n m = makeNamed (s ++ show i
  ++ (if n < 0 then "" else '_' : show n) ++ m) . PlainAxiom
       (ObjectEntity $ toO i n)

toSubClass :: Id -> [ClassExpression] -> Axiom
toSubClass i = PlainAxiom (ClassEntity $ toC i) . ListFrameBit (Just SubClass)
  . ExpressionBit . map (\ c -> ([], c))

getPropSens :: Id -> [SORT] -> Maybe SORT -> [Named Axiom]
getPropSens i args mres = let
  ncs = number args
  opOrPred = if isJust mres then "op " else "pred "
  in makeNamed (opOrPred ++ show i)
         (toSubClass i [ObjectJunction IntersectionOf
            $ maybeToList (fmap toC mres)
            ++ map (\ (a, n) -> ObjectValuesFrom SomeValuesFrom
                 (toO i n) $ toC a) ncs])
  : concatMap (\ (a, n) -> let mki = mkObjEnt opOrPred i n in
      maybeToList (fmap (mki " domain" . mkDR ADomain) mres)
      ++ [mki " range" $ mkDR ARange a]) ncs

getPropNames :: (a -> [b]) -> MapSet.MapSet Id a -> Set.Set QName
getPropNames f = Map.foldWithKey (\ i s l ->
    case Set.toList s of
      [] -> l
      h : _ -> Set.union l $ Set.fromList
        $ map (idToNumberedIRI i . snd) $ number $ f h)
    Set.empty . MapSet.toMap

commonType :: CS.Sign f e -> [[SORT]] -> Result [SORT]
commonType csig l =
  case map (keepMaximals csig) $ transpose l of
    hl | all (not . null) hl -> return $ map head hl
    _ -> fail $ "no common types for " ++ show l

commonOpType :: CS.Sign f e -> Set.Set OpType -> Result OpType
commonOpType csig os = do
  l <- commonType csig $ map (\ o -> opRes o : opArgs o) $ Set.toList os
  case l of
    r : args -> return $ mkTotOpType args r
    _ -> fail $ "no common types for " ++ showDoc os ""

commonPredType :: CS.Sign f e -> Set.Set PredType -> Result PredType
commonPredType csig ps = do
  args <- commonType csig $ map predArgs $ Set.toList ps
  case args of
    _ : _ -> return $ PredType args
    _ -> fail $ "no common types for " ++ showDoc ps ""

getCommonSupers :: CS.Sign f e -> [SORT] -> Set.Set SORT
getCommonSupers csig s = let supers t = Set.insert t $ supersortsOf t csig in
   if null s then Set.empty else foldr1 Set.intersection $ map supers s

keepMaximals :: CS.Sign f e -> [SORT] -> [SORT]
keepMaximals csig = keepMinimals1 True csig id . Set.toList
  . getCommonSupers csig

mapSign :: CS.Sign f e -> Result (OS.Sign, [Named Axiom])
mapSign csig = let
  esorts = emptySortSet csig
  srel = sortRel csig
  (eqs, subss) = eqAndSubsorts False srel
  (isos, rels) = singleAndRelatedSorts srel
  disjSorts = concatMap (\ l -> case l of
    _ : _ : _ -> [makeNamed ("disjoint " ++ show l) $ mkMisc Disjoint l]
    _ -> []) . sequence $ map (: []) isos ++ map (keepMaximals csig) rels
  ss = sortSet csig
  nsorts = Set.difference ss esorts
  mkMisc ed l = PlainAxiom (Misc []) $ ListFrameBit (Just $ EDRelation ed)
          $ ExpressionBit $ map toACE l
  eqSorts = map (\ es -> makeNamed ("equal sorts " ++ show es)
                 $ mkMisc Equivalent es) eqs
  subSens = map (\ (s, ts) -> makeNamed
    ("subsort " ++ show s ++ " of " ++ show ts) $ toSC s ts) subss
  nonEmptySens = map (\ s -> mkIndi True s [s]) $ Set.toList nsorts
  sortSens = eqSorts ++ disjSorts ++ subSens ++ nonEmptySens
  mkIndi b i ts = makeNamed
        ("individual " ++ show i ++ " of class " ++ showDoc ts "")
        $ PlainAxiom (SimpleEntity $ mkEntity NamedIndividual
        $ idToAnonIRI b i)
        $ ListFrameBit (Just Types) $ ExpressionBit
        $ map toACE ts
  om = opMap csig
  keepMaxs = keepMaximals csig
  mk s i = mkObjEnt s i (-1)
  toSC i = toSubClass i . map toC
  toIris = Set.map idToIRI
  (cs, ncs) = MapSet.partition (null . opArgs) om
  (sos, os) = MapSet.partition isSingleArgOp ncs
  (props, nps) = MapSet.partition (null . predArgs) pm
  (sps, rps') = MapSet.partition (isSingle . predArgs) nps
  (bps, ps) = MapSet.partition isBinPredType rps'
  pm = predMap csig
  osig = OS.emptySign
    { concepts = toIris $ Set.unions
      [ ss, MapSet.keysSet sps, MapSet.keysSet props
      , MapSet.keysSet os, MapSet.keysSet ps]
    , objectProperties = Set.unions
      [ toIris $ Set.union (MapSet.keysSet sos) $ MapSet.keysSet bps
      , getPropNames predArgs ps, getPropNames opArgs os ]
    , individuals = toIris $ MapSet.keysSet cs
    }
  in do
  s1 <- Map.foldWithKey (\ i s ml -> do
      l <- ml
      return $ mkIndi False i
        (keepMinimals csig id $ map opRes $ Set.toList s) : l)
    (return sortSens) (MapSet.toMap cs)
  s2 <- Map.foldWithKey (\ i s ml -> do
    l <- ml
    let sl = Set.toList s
        mki = mk "plain function " i
    case (keepMaxs $ concatMap opArgs sl, keepMaxs $ map opRes sl) of
      ([a], [r]) -> return
         $ [ mki " character" $ ListFrameBit Nothing
             $ ObjectCharacteristics [([], Functional)]
           , mki " domain" $ mkDR ADomain a, mki " range" $ mkDR ARange r]
         ++ l
      (as, rs) -> fail $ "CASL2OWL.mapSign2: " ++ show i ++ " args: "
                   ++ show as ++ " resulttypes: " ++ show rs)
    (return s1) (MapSet.toMap sos)
  s3 <- Map.foldWithKey (\ i s ml -> do
    l <- ml
    let mkp = mk "binary predicate " i
    pTy <- commonPredType csig s
    case predArgs pTy of
      [a, r] -> return
         $ [mkp " domain" $ mkDR ADomain a, mkp " range" $ mkDR ARange r]
         ++ l
      ts -> fail $ "CASL2OWL.mapSign3: " ++ show i ++ " types: " ++ show ts)
    (return s2) (MapSet.toMap bps)
  s4 <- Map.foldWithKey (\ i s ml ->
     case keepMaxs $ concatMap predArgs $ Set.toList s of
       [r] -> do
         l <- ml
         return $ makeNamed ("plain predicate " ++ show i) (toSC i [r]) : l
       ts -> fail $ "CASL2OWL.mapSign4: " ++ show i ++ " types: " ++ show ts)
     (return s3) (MapSet.toMap sps)
  s5 <- Map.foldWithKey (\ i s ml -> do
     l <- ml
     ot <- commonOpType csig s
     return $ getPropSens i (opArgs ot) (Just $ opRes ot) ++ l
     ) (return s4) (MapSet.toMap os)
  s6 <- Map.foldWithKey (\ i s ml -> do
     l <- ml
     pt <- commonPredType csig s
     return $ getPropSens i (predArgs pt) Nothing ++ l
     ) (return s5) (MapSet.toMap ps)
  return (osig, s6)

{- binary predicates and single argument functions should become
   objectProperties.
   Serge also turned constructors into concepts.
   How to treat multi-argument predicates and functions?
   Maybe create tuple concepts?
-}

mapTheory :: (FormExtension f, TermExtension f)
  => (CS.Sign f e, [Named (FORMULA f)]) -> Result (OS.Sign, [Named Axiom])
mapTheory (sig, sens) = do
  let mor = disambigSig sig
      tar = mtarget mor
      nss = map (mapNamed $ MapSen.mapMorphForm (const id) mor) sens
  (s, l) <- mapSign tar
  ll <- mapM (\ ns -> case sentence ns of
    Sort_gen_ax cs b -> return $ mapSortGenAx cs b
    _ -> flip (hint []) nullRange
         . ("not translated\n" ++) . show . printTheoryFormula
         $ mapNamed (simplifySen (const return) (const id) tar) ns
             ) nss
  return (s, l ++ concat ll)

mapSortGenAx :: [Constraint] -> Bool -> [Named Axiom]
mapSortGenAx cs b = map (\ (s, as) ->
  let is = map (\ (Qual_op_name n ty _) -> case args_OP_TYPE ty of
                [] -> ObjectOneOf [idToIRI n]
                [_] -> ObjectValuesFrom SomeValuesFrom (toO n (-1)) $ toC s
                _ -> toC n) as
  in makeNamed ("generated " ++ show s)
         $ PlainAxiom (ClassEntity $ toC s)
         $ if b && not (isSingle is) then AnnFrameBit [] $ ClassDisjointUnion is
           else ListFrameBit (Just $ EDRelation Equivalent)
             $ ExpressionBit [([], case is of
                 [i] -> i
                 _ -> ObjectJunction UnionOf is)])
  $ recoverSortGen cs
