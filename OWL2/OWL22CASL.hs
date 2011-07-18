{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  Comorphism from OWL 2 to CASL_Dl
Copyright   :  (c) Francisc-Nicolae BungiuObjectPropertyFacts EntityType
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.bungiu@jacobs-university.de
Stability   :  provisional
Portability :  non-portable (via Logic.Logic)
-}

module OWL2.OWL22CASL (OWL22CASL (..)) where

import Logic.Logic as Logic
import Logic.Comorphism
import Common.AS_Annotation
import Common.Result
import Common.Id
import Control.Monad
import Data.Char
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Common.Lib.MapSet as MapSet
import qualified Common.Lib.Rel as Rel

-- the DL with the initial signature for OWL
import CASL_DL.PredefinedCASLAxioms

-- OWL = domain
import OWL2.Logic_OWL2
import OWL2.MS
import OWL2.AS
import OWL2.Sublogic
import OWL2.ManchesterPrint ()
import OWL2.Morphism
import OWL2.Symbols
import qualified OWL2.Sign as OS
-- CASL_DL = codomain
import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism
import CASL.Sublogic

import Common.ProofTree

import Data.Maybe

data OWL22CASL = OWL22CASL deriving Show

instance Language OWL22CASL

instance Comorphism
    OWL22CASL        -- comorphism
    OWL2             -- lid domain
    OWLSub          -- sublogics domain
    OntologyDocument    -- Basic spec domain
    Axiom           -- sentence domain
    SymbItems       -- symbol items domain
    SymbMapItems    -- symbol map items domain
    OS.Sign         -- signature domain
    OWLMorphism     -- morphism domain
    Entity          -- symbol domain
    RawSymb         -- rawsymbol domain
    ProofTree       -- proof tree codomain
    CASL            -- lid codomain
    CASL_Sublogics  -- sublogics codomain
    CASLBasicSpec   -- Basic spec codomain
    CASLFORMULA     -- sentence codomain
    SYMB_ITEMS      -- symbol items codomain
    SYMB_MAP_ITEMS  -- symbol map items codomain
    CASLSign        -- signature codomain
    CASLMor         -- morphism codomain
    Symbol          -- symbol codomain
    RawSymbol       -- rawsymbol codomain
    ProofTree       -- proof tree domain
    where
      sourceLogic OWL22CASL = OWL2
      sourceSublogic OWL22CASL = sl_top
      targetLogic OWL22CASL = CASL
      mapSublogic OWL22CASL _ = Just $ cFol
        { cons_features = emptyMapConsFeature }
      map_theory OWL22CASL = mapTheory
      map_morphism OWL22CASL = mapMorphism
      isInclusionComorphism OWL22CASL = True
      has_model_expansion OWL22CASL = True

-- | Mapping of OWL morphisms to CASL morphisms
mapMorphism :: OWLMorphism -> Result CASLMor
mapMorphism oMor =
    do
      cdm <- mapSign $ osource oMor
      ccd <- mapSign $ otarget oMor
      let emap = mmaps oMor
          preds = Map.foldWithKey (\ (Entity ty u1) u2 -> let
              i1 = uriToId u1
              i2 = uriToId u2
              in case ty of
                Class -> Map.insert (i1, conceptPred) i2
                ObjectProperty -> Map.insert (i1, objectPropPred) i2
                DataProperty -> Map.insert (i1, dataPropPred) i2
                _ -> id) Map.empty emap
          ops = Map.foldWithKey (\ (Entity ty u1) u2 -> case ty of
                NamedIndividual ->
                    Map.insert (uriToId u1, indiConst) (uriToId u2, Total)
                _ -> id) Map.empty emap
      return (embedMorphism () cdm ccd)
                 { op_map = ops
                 , pred_map = preds }

data VarOrIndi = OVar Int | OIndi IRI

objectPropPred :: PredType
objectPropPred = PredType [thing, thing]

dataPropPred :: PredType
dataPropPred = PredType [thing, dataS]

indiConst :: OpType
indiConst = OpType Total [] thing

mapSign :: OS.Sign                 -- ^ OWL signature
        -> Result CASLSign         -- ^ CASL signature
mapSign sig =
      let conc = OS.concepts sig
          cvrt = map uriToId . Set.toList
          tMp k = MapSet.fromList . map (\ u -> (u, [k]))
          cPreds = thing : nothing : cvrt conc
          oPreds = cvrt $ OS.objectProperties sig
          dPreds = cvrt $ OS.dataProperties sig
          aPreds = foldr MapSet.union MapSet.empty
            [ tMp conceptPred cPreds
            , tMp objectPropPred oPreds
            , tMp dataPropPred dPreds ]
     in return $ uniteCASLSign predefSign (emptySign ())
             { predMap = aPreds
             , opMap = tMp indiConst . cvrt $ OS.individuals sig
             }


loadDataInformation :: OWLSub -> Sign f ()
loadDataInformation _ =
    let
        dts = Set.fromList $ map stringToId datatypeKeys
    in
     (emptySign ()) { sortRel = Rel.fromKeysSet dts }

mapTheory :: (OS.Sign, [Named Axiom])
             -> Result (CASLSign, [Named CASLFORMULA])
mapTheory (owlSig, owlSens) =
        let
            sublogic = sl_top
        in
    do
      cSig <- mapSign owlSig
      let pSig = loadDataInformation sublogic
      (cSens, nSig) <- foldM (\ (x, y) z ->
                           do
                             (sen, sig) <- mapSentence y z
                             return (sen ++ x, uniteCASLSign sig y)
                             ) ([], cSig) owlSens
      return (uniteCASLSign nSig pSig, predefinedAxioms ++ cSens)

-- | mapping of OWL to CASL_DL formulae
mapSentence :: CASLSign                           -- ^ CASL Signature
  -> Named Axiom                                  -- ^ OWL2 Sentence
  -> Result ([Named CASLFORMULA], CASLSign) -- ^ CASL Sentence
mapSentence cSig inSen = do
    (outAx, outSig) <- mapAxioms cSig $ sentence inSen
    return (map (flip mapNamed inSen . const) outAx, outSig)

mapAxioms :: CASLSign
          -> Axiom
          -> Result ([CASLFORMULA], CASLSign)
mapAxioms cSig ax =
  case ax of
    PlainAxiom ex fb ->
      case fb of
        ListFrameBit rel lfb ->
          mapListFrameBit cSig ex rel lfb
        AnnFrameBit _anno afb ->
          mapAnnFrameBit cSig ex afb


toIRILst :: EntityType
         -> Extended
         -> Maybe IRI

toIRILst ty ane = case ane of
  SimpleEntity (Entity ty2 iri) | ty == ty2 -> Just iri
  _ -> Nothing


-- | Mapping of ListFrameBit
mapListFrameBit :: CASLSign
       -> Extended
       -> Maybe Relation
       -> ListFrameBit
       -> Result ([CASLFORMULA], CASLSign)
mapListFrameBit cSig ex rel lfb = case lfb of
    AnnotationBit _a -> return ([], cSig)
    ExpressionBit cls ->
      case ex of
          Misc _ -> return ([], cSig)
          SimpleEntity (Entity ty iri) ->
            case ty of
              NamedIndividual | rel == Just Types ->
                do
                  inD <- mapIndivURI cSig iri
                  ocls <- mapM (\ (_, c) -> mapDescription cSig c 1) cls
                  return (map (\ cd -> Quantification Universal
                             [Var_decl [mkNName 1] thing nullRange]
                             (
                              Implication
                              (Strong_equation
                               (Qual_var (mkNName 1) thing nullRange)
                               inD
                               nullRange
                              ) cd
                              True
                              nullRange
                             )
                             nullRange) ocls, cSig)

              DataProperty | rel == (Just $ DRRelation ADomain) ->
                do
                  oEx <- mapDataProp cSig iri 1 2
                  odes <- mapM (\ (_, c) -> mapDescription cSig c 1) cls
                  let vars = (mkNName 1, mkNName 2)
                  return (map (\ cd -> Quantification Universal
                          [Var_decl [fst vars] thing nullRange]
                          (Quantification Existential
                          [Var_decl [snd vars] dataS nullRange]
                          (Implication oEx cd True nullRange)
                          nullRange) nullRange) odes, cSig)


              _ -> return ([], cSig)
          ObjectEntity oe ->
            case rel of
              Nothing -> return ([], cSig)
              Just re ->
                case re of
                  DRRelation r -> do
                    tobjP <- mapObjProp cSig oe 1 2
                    tdsc <- mapM (\ (_, c) -> mapDescription cSig c $
                      case r of
                        ADomain -> 1
                        ARange -> 2) cls
                    let vars = case r of
                                 ADomain -> (mkNName 1, mkNName 2)
                                 ARange -> (mkNName 2, mkNName 1)
                    return (map (\ cd -> mkForallRange
                                     [Var_decl [fst vars] thing nullRange]
                                     (
                                      Quantification Existential
                                         [Var_decl [snd vars] thing nullRange]
                                         (
                                          Implication
                                           tobjP
                                           cd
                                          True
                                          nullRange
                                         )
                                      nullRange
                                     )
                                     nullRange) tdsc, cSig)
                  _ -> fail "ObjectEntity Relation nyi"
          ClassEntity ce -> do
            let map2nd = map snd cls
            case rel of
              Nothing -> return ([], cSig)
              Just r -> case r of
                EDRelation re ->
                  do
                    decrsS <- mapDescriptionListP cSig 1
                      $ comPairsaux ce map2nd
                    let decrsP = map (\ (x, y) ->
                            mkForallRange
                              [Var_decl [mkNName 1] thing nullRange]
                            (case re of
                              Equivalent ->
                                  Equivalence x y nullRange
                              Disjoint ->
                                  Negation
                                       (Conjunction [x, y] nullRange) nullRange)
                             nullRange)
                                  decrsS
                    return (decrsP, cSig)
                SubClass ->
                  do
                    domT <- mapDescription cSig ce 1
                    codT <- mapDescriptionList cSig 1 map2nd
                    return (map (\ cd -> mkForallRange
                               [Var_decl [mkNName 1] thing nullRange]
                               (Implication
                                domT
                                cd
                                True
                                nullRange) nullRange) codT, cSig)
                _ -> fail "ClassEntity Relation nyi"

    ObjectBit ol ->
      let mol = fmap ObjectProp (toIRILst ObjectProperty ex)
          isJ = isJust mol
          Just ob = mol
          map2nd = map snd ol
      in case rel of
      Nothing -> return ([], cSig)
      Just r -> case r of
        EDRelation ed -> do
          pairs <- mapComObjectPropsList cSig mol map2nd 1 2
          return (map (\ (a, b) -> mkForallRange
                              [ Var_decl [mkNName 1] thing nullRange
                              , Var_decl [mkNName 2] thing nullRange]
                                 (case ed of
                                   Equivalent ->
                                                Equivalence a b nullRange
                                   Disjoint ->
                                                 Negation
                                                 (Conjunction [a, b] nullRange)
                                                 nullRange)
                               nullRange) pairs, cSig)
        SubPropertyOf | isJ -> do
                  os <- mapM (\ (o1, o2) -> mapSubObjProp cSig o1 o2 3)
                    $ comPairsaux ob map2nd
                  return (os, cSig)
        InverseOf | isJ ->
          do
             os1 <- mapM (\ o1 -> mapObjProp cSig o1 1 2) map2nd
             o2 <- mapObjProp cSig ob 2 1
             return (map (\ o1 -> mkForallRange
                             [Var_decl [mkNName 1] thing nullRange
                             , Var_decl [mkNName 2] thing nullRange]
                             (
                              Equivalence
                              o2
                              o1
                              nullRange
                             )
                             nullRange) os1, cSig)
        _ -> return ([], cSig)

    DataBit db ->
      let mol = toIRILst DataProperty ex
          isJ = isJust mol
          map2nd = map snd db
          Just ob = mol
      in case rel of
      Nothing -> return ([], cSig)
      Just r -> case r of
        SubPropertyOf | isJ -> do
          os1 <- mapM (\ o1 -> mapDataProp cSig o1 1 2) map2nd
          o2 <- mapDataProp cSig ob 2 1
          return (map (\ o1 -> mkForallRange
                               [ Var_decl [mkNName 1] thing nullRange
                               , Var_decl [mkNName 2] dataS nullRange]
                               (
                                Implication
                                o2
                                o1
                                True
                                nullRange
                               )
                               nullRange) os1, cSig)
        EDRelation ed -> do
          pairs <- mapComDataPropsList cSig map2nd 1 2
          return (map (\ (a, b) -> mkForallRange
                              [ Var_decl [mkNName 1] thing nullRange
                              , Var_decl [mkNName 2] dataS nullRange]
                                (case ed of
                                   Equivalent ->
                                     Equivalence a b nullRange
                                   Disjoint ->
                                     Negation
                                       (Conjunction [a, b] nullRange)
                                       nullRange)
                               nullRange) pairs, cSig)
        _ -> return ([], cSig)

    IndividualSameOrDifferent al ->
      do
        let mol = toIRILst NamedIndividual ex
            map2nd = map snd al
        case rel of
          Nothing -> return ([], cSig)
          Just r ->
            case r of
              SDRelation re -> do
                fs <- mapComIndivList cSig re mol map2nd
                return (fs, cSig)
              _ -> return ([], cSig)

    DataPropRange dpr ->
      case rel of
        Nothing -> return ([], cSig)
        Just re ->
          case re of
            DRRelation r ->
              case r of
                 ARange ->
                      case ex of
                        SimpleEntity ent ->
                          case ent of
                            Entity ty iri ->
                              case ty of
                                DataProperty ->
                                  do
                                    oEx <- mapDataProp cSig iri 1 2
                                    odes <- mapM (\ (_, c) ->
                                                  mapDataRange cSig c 2) dpr
                                    let vars = (mkNName 1, mkNName 2)
                                    return (map (\ cd -> mkForallRange
                                         [Var_decl [fst vars] thing nullRange]
                                         (Quantification Existential
                                         [Var_decl [snd vars] dataS nullRange]
                                         (Implication oEx cd True nullRange)
                                         nullRange) nullRange) odes, cSig)
                                _ -> fail "DataPropRange EntityType fail"
                        _ -> fail "DataPropRange Entity fail"
                 _ -> fail "DataPropRange ADomain ni"
            _ -> fail "DataPropRange Relations ni"
    IndividualFacts indf ->
        let map2nd = map snd indf
        in
        case map2nd of
          [ObjectPropertyFact posneg obe ind] ->
            case ex of
              SimpleEntity (Entity NamedIndividual siri) ->
                    do
                      inS <- mapIndivURI cSig siri
                      inT <- mapIndivURI cSig ind
                      oPropH <- mapObjProp cSig obe 1 2
                      let oProp = case posneg of
                                      Positive -> oPropH
                                      Negative -> Negation oPropH nullRange
                      return ([mkForallRange
                                     [Var_decl [mkNName 1]
                                         thing nullRange
                                      , Var_decl [mkNName 2]
                                         thing nullRange]
                                      (
                                       Implication
                                       (
                                        Conjunction
                                        [
                                        Strong_equation
                                         (Qual_var (mkNName 1) thing
                                          nullRange)
                                          inS
                                          nullRange
                                          , Strong_equation
                                          (Qual_var (mkNName 2) thing
                                           nullRange)
                                          inT
                                          nullRange
                                         ]
                                         nullRange
                                        )
                                        oProp
                                        True
                                       nullRange
                                      )
                                 nullRange], cSig)
              _ -> fail $ "ObjectPropertyFactsFacts Entity fail: " ++ show ex
          [DataPropertyFact posneg dpe lit] ->
            case ex of
              SimpleEntity (Entity ty iri) ->
                case ty of
                  DataProperty ->
                    do
                      inS <- mapIndivURI cSig iri
                      inT <- mapLiteral cSig lit
                      oPropH <- mapDataProp cSig dpe 1 2
                      let oProp = case posneg of
                                    Positive -> oPropH
                                    Negative -> Negation oPropH nullRange
                      return ([mkForallRange
                                           [Var_decl [mkNName 1]
                                                     thing nullRange
                                           , Var_decl [mkNName 2]
                                                     thing nullRange]
                                         (
                                          Implication
                                          (
                                           Conjunction
                                           [
                                            Strong_equation
                                            (Qual_var (mkNName 1) thing
                                             nullRange)
                                            inS
                                            nullRange
                                           , Strong_equation
                                            (Qual_var (mkNName 2) thing
                                             nullRange)
                                            inT
                                            nullRange
                                           ]
                                           nullRange
                                          )
                                           oProp
                                          True
                                          nullRange
                                         )
                                         nullRange], cSig)
                  _ -> fail "DataPropertyFact EntityType fail"
              _ -> fail "DataPropertyFact Entity fail"
          _ -> fail "DataPropertyFacts fail"
    ObjectCharacteristics ace ->
      let map2nd = map snd ace
      in
      case ex of
        ObjectEntity ope ->
          case map2nd of
            [Functional] ->
              do
                so1 <- mapObjProp cSig ope 1 2
                so2 <- mapObjProp cSig ope 1 3
                return ([mkForallRange
                                     [Var_decl [mkNName 1] thing nullRange
                                     , Var_decl [mkNName 2] thing nullRange
                                     , Var_decl [mkNName 3] thing nullRange
                                     ]
                                     (
                                      Implication
                                      (
                                       Conjunction [so1, so2] nullRange
                                      )
                                      (
                                       Strong_equation
                                       (
                                        Qual_var (mkNName 2) thing nullRange
                                       )
                                       (
                                        Qual_var (mkNName 3) thing nullRange
                                       )
                                       nullRange
                                      )
                                      True
                                      nullRange
                                     )
                                     nullRange], cSig)
            [InverseFunctional] ->
               do
                 so1 <- mapObjProp cSig ope 1 3
                 so2 <- mapObjProp cSig ope 2 3
                 return ([mkForallRange
                                     [Var_decl [mkNName 1] thing nullRange
                                     , Var_decl [mkNName 2] thing nullRange
                                     , Var_decl [mkNName 3] thing nullRange
                                     ]
                                     (
                                      Implication
                                      (
                                       Conjunction [so1, so2] nullRange
                                      )
                                      (
                                       Strong_equation
                                       (
                                        Qual_var (mkNName 1) thing nullRange
                                       )
                                       (
                                        Qual_var (mkNName 2) thing nullRange
                                       )
                                       nullRange
                                      )
                                      True
                                      nullRange
                                     )
                                     nullRange], cSig)
            [Reflexive] ->
              do
                so <- mapObjProp cSig ope 1 1
                return ([mkForallRange
                                   [Var_decl [mkNName 1] thing nullRange]
                                   (
                                    Implication
                                     (
                                      Membership
                                      (Qual_var (mkNName 1) thing nullRange)
                                      thing
                                      nullRange
                                     )
                                     so
                                     True
                                     nullRange
                                   )
                                   nullRange], cSig)
            [Irreflexive] ->
              do
                so <- mapObjProp cSig ope 1 1
                return ([mkForallRange
                                   [Var_decl [mkNName 1] thing nullRange]
                                   (
                                    Implication
                                    (
                                     Membership
                                     (Qual_var (mkNName 1) thing nullRange)
                                     thing
                                     nullRange
                                    )
                                    (
                                     Negation
                                     so
                                    nullRange
                                    )
                                    True
                                    nullRange
                                   )
                                   nullRange], cSig)
            [Symmetric] ->
              do
                 so1 <- mapObjProp cSig ope 1 2
                 so2 <- mapObjProp cSig ope 2 1
                 return
                           ([mkForallRange
                               [Var_decl [mkNName 1] thing nullRange
                               , Var_decl [mkNName 2] thing nullRange]
                               (
                                Implication
                                so1
                                so2
                                True
                                nullRange
                               )
                               nullRange], cSig)
            [Asymmetric] ->
              do
                so1 <- mapObjProp cSig ope 1 2
                so2 <- mapObjProp cSig ope 2 1
                return ([mkForallRange
                               [Var_decl [mkNName 1] thing nullRange
                               , Var_decl [mkNName 2] thing nullRange]
                               (
                                Implication
                                so1
                                (Negation so2 nullRange)
                                True
                                nullRange
                               )
                               nullRange], cSig)
            [Antisymmetric] ->
              do
                so1 <- mapObjProp cSig ope 1 2
                so2 <- mapObjProp cSig ope 2 1
                return ([mkForallRange
                               [Var_decl [mkNName 1] thing nullRange
                               , Var_decl [mkNName 2] thing nullRange]
                               (
                                Implication
                                 (Conjunction [so1, so2] nullRange)
                                 (
                                  Strong_equation
                                  (
                                   Qual_var (mkNName 1) thing nullRange
                                  )
                                  (
                                   Qual_var (mkNName 2) thing nullRange
                                  )
                                  nullRange
                                 )
                                True
                                nullRange
                               )
                               nullRange], cSig)
            [Transitive] ->
              do
                so1 <- mapObjProp cSig ope 1 2
                so2 <- mapObjProp cSig ope 2 3
                so3 <- mapObjProp cSig ope 1 3
                return ([mkForallRange
                               [Var_decl [mkNName 1] thing nullRange
                               , Var_decl [mkNName 2] thing nullRange
                               , Var_decl [mkNName 3] thing nullRange]
                               (
                                Implication
                                (
                                 Conjunction [so1, so2] nullRange
                                )
                                 so3
                                True
                                nullRange
                               )
                               nullRange], cSig)
            _ -> fail "ObjectCharacteristics Character fail"
        _ -> fail "ObjectCharacteristics Entity fail"

-- | Mapping of AnnFrameBit
mapAnnFrameBit :: CASLSign
       -> Extended
       -> AnnFrameBit
       -> Result ([CASLFORMULA], CASLSign)
mapAnnFrameBit cSig ex afb =
  case afb of
    AnnotationFrameBit -> return ([], cSig)
    DataFunctional ->
      case ex of
        SimpleEntity (Entity ty iri) ->
          case ty of
            DataProperty ->
              do
                so1 <- mapDataProp cSig iri 1 2
                so2 <- mapDataProp cSig iri 1 3
                return ([mkForallRange
                                     [Var_decl [mkNName 1] thing nullRange
                                     , Var_decl [mkNName 2] dataS nullRange
                                     , Var_decl [mkNName 3] dataS nullRange
                                     ]
                                     (
                                      Implication
                                      (
                                       Conjunction [so1, so2] nullRange
                                      )
                                      (
                                       Strong_equation
                                       (
                                        Qual_var (mkNName 2) dataS nullRange
                                       )
                                       (
                                        Qual_var (mkNName 3) dataS nullRange
                                       )
                                       nullRange
                                      )
                                      True
                                      nullRange
                                     )
                                    nullRange], cSig)
            _ -> fail "DataFunctional EntityType fail"
        _ -> fail "DataFunctional Extend fail"
    DatatypeBit dr ->
      case ex of
        SimpleEntity (Entity ty iri) ->
          case ty of
            Datatype ->
              do
                odes <- mapDataRange cSig dr 2
                let dtb = uriToId iri
                return ([mkForallRange
                          [Var_decl [mkNName 1] thing nullRange]
                            (
                            Equivalence
                             odes
                             (Membership
                              (Qual_var (mkNName 2) thing nullRange)
                             dtb
                             nullRange
                             )
                            nullRange
                            )
                       nullRange]
                       , cSig)
            _ -> fail "DatatypeBit EntityType fail"
        _ -> fail "DatatypeBit Extend fail"
    ClassDisjointUnion clsl ->
      case ex of
        SimpleEntity (Entity ty iri) ->
          case ty of
            Class ->
              do
                 decrs <- mapDescriptionList cSig 1 clsl
                 decrsS <- mapDescriptionListP cSig 1 $ comPairs clsl clsl
                 let decrsP = map (\ (x, y) -> conjunct [x, y]) decrsS
                 mcls <- mapClassURI cSig iri (mkNName 1)
                 return ([mkForallRange
                              [Var_decl [mkNName 1] thing nullRange]
                               (
                                Equivalence
                                  mcls
                                (
                                  Conjunction
                                  [
                                   Disjunction decrs nullRange
                                  , Negation
                                   (
                                    Conjunction decrsP nullRange
                                   )
                                   nullRange
                                  ]
                                  nullRange
                                )
                                nullRange
                               ) nullRange], cSig)
            _ -> fail "ClassDisjointUnion EntityType fail"
        _ -> fail "ClassDisjointUnion Extend fail"
    ClassHasKey _obpe _dpe -> return ([], cSig)
    ObjectSubPropertyChain oplst ->
      do
        os <- mapM (\ cd -> mapSubObjPropChain cSig afb cd 3) oplst
        return (os, cSig)

-- | Mapping of ObjectSubPropertyChain
mapSubObjPropChain :: CASLSign
              -> AnnFrameBit
              -> ObjectPropertyExpression
              -> Int
              -> Result CASLFORMULA
mapSubObjPropChain cSig prop oP num1 =
    let num2 = num1 + 1
    in
    case prop of
           ObjectSubPropertyChain props ->
             do
               let zprops = zip (tail props) [(num2 + 1) ..]
                   (_, vars) = unzip zprops
               oProps <- mapM (\ (z, x, y) -> mapObjProp cSig z x y) $
                                 zip3 props ((num1 : vars) ++ [num2]) $
                                      tail ((num1 : vars) ++ [num2])
               ooP <- mapObjProp cSig oP num1 num2
               return $ mkForallRange
                     [ Var_decl [mkNName num1] thing nullRange
                     , Var_decl [mkNName num2] thing nullRange]
                     (
                      mkForallRange
                         (
                          map (\ x -> Var_decl [mkNName x] thing nullRange) vars
                         )
                         (
                          Implication
                          (Conjunction oProps nullRange)
                          ooP
                          True
                          nullRange
                         )
                       nullRange
                     )
                    nullRange
           _ -> fail "mapping of ObjectSubPropertyChain failed"


{- | Mapping along ObjectPropsList for creation of pairs for commutative
operations. -}
mapComObjectPropsList :: CASLSign                    -- ^ CASLSignature
                      -> Maybe ObjectPropertyExpression
                      -> [ObjectPropertyExpression]
                      -> Int                         -- ^ First variable
                      -> Int                         -- ^ Last  variable
                      -> Result [(CASLFORMULA, CASLFORMULA)]
mapComObjectPropsList cSig mol props num1 num2 = do
  fs <- mapM (\ x -> mapObjProp cSig x num1 num2) props
  case mol of
    Nothing -> return $ comPairs fs fs
    Just ol -> do
      f <- mapObjProp cSig ol num1 num2
      return $ comPairsaux f fs

mapComIndivList :: CASLSign                    -- ^ CASLSignature
                -> SameOrDifferent
                -> Maybe Individual
                -> [Individual]
                -> Result [CASLFORMULA]
mapComIndivList cSig sod mol inds = do
  fs <- mapM (mapIndivURI cSig) inds
  tps <- case mol of
    Nothing -> return $ comPairs fs fs
    Just ol -> do
      f <- mapIndivURI cSig ol
      return $ comPairsaux f fs
  return $ map (\ (x, y) -> case sod of
    Same -> mkStEq x y
    Different -> Negation (mkStEq x y) nullRange) tps


-- | mapping of data constants
mapLiteral :: CASLSign
            -> Literal
            -> Result (TERM ())
mapLiteral _ c =
    do
      let cl = case c of
                Literal l _ -> l
      return $ Application
               (
                Qual_op_name
                (stringToId cl)
                (Op_type Total [] dataS nullRange)
                nullRange
               )
               []
               nullRange

-- | Mapping of subobj properties
mapSubObjProp :: CASLSign
              -> ObjectPropertyExpression
              -> ObjectPropertyExpression
              -> Int
              -> Result CASLFORMULA
mapSubObjProp cSig oPL oP num1 = do
    let num2 = num1 + 1
    l <- mapObjProp cSig oPL num1 num2
    r <- mapObjProp cSig oP num1 num2
    return $ mkForallRange [mkVarDecl (mkNName num1) thing,
                       mkVarDecl (mkNName num2) thing]
                       (mkImpl r l )
                       nullRange

{- | Mapping along DataPropsList for creation of pairs for commutative
operations. -}
mapComDataPropsList :: CASLSign
                      -> [DataPropertyExpression]
                      -> Int                         -- ^ First variable
                      -> Int                         -- ^ Last  variable
                      -> Result [(CASLFORMULA, CASLFORMULA)]
mapComDataPropsList cSig props num1 num2 =
      mapM (\ (x, z) -> do
                              l <- mapDataProp cSig x num1 num2
                              r <- mapDataProp cSig z num1 num2
                              return (l, r)
                       ) $ comPairs props props

-- | Mapping of data properties
mapDataProp :: CASLSign
            -> DataPropertyExpression
            -> Int
            -> Int
            -> Result CASLFORMULA
mapDataProp _ dP nO nD =
    do
      let
          l = mkNName nO
          r = mkNName nD
      ur <- uriToIdM dP
      return $ Predication
                 (Qual_pred_name ur (toPRED_TYPE dataPropPred) nullRange)
                 [Qual_var l thing nullRange, Qual_var r dataS nullRange]
                 nullRange

-- | Mapping of obj props
mapObjProp :: CASLSign
              -> ObjectPropertyExpression
              -> Int
              -> Int
              -> Result CASLFORMULA
mapObjProp cSig ob num1 num2 =
    case ob of
      ObjectProp u ->
          do
            let l = mkNName num1
                r = mkNName num2
            ur <- uriToIdM u
            return $ Predication
              (Qual_pred_name ur (toPRED_TYPE objectPropPred) nullRange)
              [Qual_var l thing nullRange, Qual_var r thing nullRange]
              nullRange
      ObjectInverseOf u ->
          mapObjProp cSig u num2 num1

-- | Mapping of obj props with Individuals
mapObjPropI :: CASLSign
              -> ObjectPropertyExpression
              -> VarOrIndi
              -> VarOrIndi
              -> Result CASLFORMULA
mapObjPropI cSig ob lP rP =
      case ob of
        ObjectProp u ->
          do
            lT <- case lP of
                    OVar num1 -> return $ Qual_var (mkNName num1)
                                     thing nullRange
                    OIndi indivID -> mapIndivURI cSig indivID
            rT <- case rP of
                    OVar num1 -> return $ Qual_var (mkNName num1)
                                     thing nullRange
                    OIndi indivID -> mapIndivURI cSig indivID
            ur <- uriToIdM u
            return $ Predication
                       (Qual_pred_name ur
                        (toPRED_TYPE objectPropPred) nullRange)
                       [lT,
                        rT
                       ]
                       nullRange
        ObjectInverseOf u -> mapObjPropI cSig u rP lP

-- | Mapping of Class URIs
mapClassURI :: CASLSign
            -> Class
            -> Token
            -> Result CASLFORMULA
mapClassURI _ uril uid =
    do
      ur <- uriToIdM uril
      return $ Predication
                  (Qual_pred_name ur (toPRED_TYPE conceptPred) nullRange)
                  [Qual_var uid thing nullRange]
                  nullRange

-- | Mapping of Individual URIs
mapIndivURI :: CASLSign
            -> Individual
            -> Result (TERM ())
mapIndivURI _ uriI =
    do
      ur <- uriToIdM uriI
      return $ Application
                 (
                  Qual_op_name
                  ur
                  (Op_type Total [] thing nullRange)
                  nullRange
                 )
                 []
                 nullRange

uriToIdM :: IRI -> Result Id
uriToIdM = return . uriToId

-- | Extracts Id from URI
uriToId :: IRI -> Id
uriToId urI =
    let l = localPart urI
        ur = if elem l ["Thing", "Nothing"] then mkQName l else urI
        repl a = if isAlphaNum a
                  then
                      a
                  else
                      '_'
        nP = map repl $ namePrefix ur
        lP = map repl l
    in stringToId $ nP ++ "" ++ lP

-- | Mapping of a list of descriptions
mapDescriptionList :: CASLSign
                      -> Int
                      -> [ClassExpression]
                      -> Result [CASLFORMULA]
mapDescriptionList cSig n lst =
      mapM (uncurry $ mapDescription cSig)
                                $ zip lst $ replicate (length lst) n

-- | Mapping of a list of pairs of descriptions
mapDescriptionListP :: CASLSign
                    -> Int
                    -> [(ClassExpression, ClassExpression)]
                    -> Result [(CASLFORMULA, CASLFORMULA)]
mapDescriptionListP cSig n lst =
    do
      let (l, r) = unzip lst
      llst <- mapDescriptionList cSig n l
      rlst <- mapDescriptionList cSig n r
      let olst = zip llst rlst
      return olst

-- | Get all distinct pairs for commutative operations
comPairs :: [t] -> [t1] -> [(t, t1)]
comPairs [] [] = []
comPairs _ [] = []
comPairs [] _ = []
comPairs (a : as) (_ : bs) = comPairsaux a bs ++ comPairs as bs

comPairsaux :: t -> [t1] -> [(t, t1)]
comPairsaux a = map (\ b -> (a, b))

-- | mapping of Data Range
mapDataRange :: CASLSign
          -> DataRange
          -> Int
          -> Result CASLFORMULA
mapDataRange cSig dr inId =
    do
        let uid = mkNName inId
        case dr of
          DataType d _ ->
            do
              ur <- uriToIdM d
              return $ Membership
                        (Qual_var uid thing nullRange)
                        ur
                        nullRange
          DataComplementOf drc ->
            do
              dc <- mapDataRange cSig drc inId
              return $ Negation dc nullRange
          DataOneOf _ -> error "nyi"
          DataJunction _ _ -> error "nyi"

-- | mapping of OWL2 Descriptions
mapDescription :: CASLSign
                -> ClassExpression
                -> Int
                -> Result CASLFORMULA
mapDescription cSig desc var = case desc of
    Expression u -> mapClassURI cSig u (mkNName var)
    ObjectJunction ty ds ->
        do
           des0 <- mapM (flip (mapDescription cSig) var) ds
           return $ case ty of
                UnionOf -> Disjunction des0 nullRange
                IntersectionOf -> Conjunction des0 nullRange
    ObjectComplementOf d ->
        do
           des0 <- mapDescription cSig d var
           return $ Negation des0 nullRange
    ObjectOneOf is ->
        do
           ind0 <- mapM (mapIndivURI cSig) is
           let var0 = Qual_var (mkNName var) thing nullRange
           let forms = map (mkStEq var0) ind0
           return $ Disjunction forms nullRange
    ObjectValuesFrom ty o d ->
        do
           oprop0 <- mapObjProp cSig o var (var + 1)
           desc0 <- mapDescription cSig d (var + 1)
           case ty of
                SomeValuesFrom ->
                   return $ Quantification Existential [Var_decl [mkNName
                                                                   (var + 1)]
                                                          thing nullRange]
                          (
                          Conjunction
                           [oprop0, desc0]
                           nullRange
                          )
                          nullRange
                AllValuesFrom ->
                   return $ mkForallRange [Var_decl [mkNName
                                                               (var + 1)]
                                                       thing nullRange]
                       (
                        Implication
                        oprop0 desc0
                        True
                        nullRange
                       )
                       nullRange
    ObjectHasSelf o -> mapObjProp cSig o var var
    ObjectHasValue o i ->
        mapObjPropI cSig o (OVar var) (OIndi i)
    ObjectCardinality c ->
        case c of
           Cardinality ct n oprop d
                ->
                   do
                     let vlst = [(var + 1) .. (n + var)]
                         vlstM = [(var + 1) .. (n + var + 1)]
                     dOut <- (\ x -> case x of
                                     Nothing -> return []
                                     Just y ->
                                           mapM (mapDescription cSig y) vlst
                                ) d
                     let dlst = map (\ (x, y) ->
                                     Negation
                                     (
                                        Strong_equation
                                         (Qual_var (mkNName x) thing nullRange)
                                         (Qual_var (mkNName y) thing nullRange)
                                         nullRange
                                     )
                                     nullRange
                                    ) $ comPairs vlst vlst
                         dlstM = map (\ (x, y) ->
                                      Strong_equation
                                      (Qual_var (mkNName x) thing nullRange)
                                      (Qual_var (mkNName y) thing nullRange)
                                      nullRange
                                     ) $ comPairs vlstM vlstM
                         qVars = map (\ x ->
                                      Var_decl [mkNName x]
                                                thing nullRange
                                     ) vlst
                         qVarsM = map (\ x ->
                                       Var_decl [mkNName x]
                                                 thing nullRange
                                      ) vlstM
                     oProps <- mapM (mapObjProp cSig oprop var) vlst
                     oPropsM <- mapM (mapObjProp cSig oprop var) vlstM
                     let minLst = Quantification Existential
                                  qVars
                                  (
                                   Conjunction
                                   (dlst ++ dOut ++ oProps)
                                   nullRange
                                  )
                                  nullRange
                     let maxLst = mkForallRange
                                  qVarsM
                                  (
                                   Implication
                                   (Conjunction (oPropsM ++ dOut) nullRange)
                                   (Disjunction dlstM nullRange)
                                   True
                                   nullRange
                                  )
                                  nullRange
                     case ct of
                        MinCardinality -> return minLst
                        MaxCardinality -> return maxLst
                        ExactCardinality -> return $
                                            Conjunction
                                            [minLst, maxLst]
                                            nullRange
    DataValuesFrom ty dpe dr ->
      do
        oprop0 <- mapDataProp cSig dpe var (var + 1)
        desc0 <- mapDataRange cSig dr (var + 1)
        case ty of
                SomeValuesFrom ->
                   return $ Quantification Existential [Var_decl [mkNName
                                                                   (var + 1)]
                                                          thing nullRange]
                          (
                          Conjunction
                           [oprop0, desc0]
                           nullRange
                          )
                          nullRange
                AllValuesFrom ->
                   return $ mkForallRange
                       [Var_decl [mkNName (var + 1)] thing nullRange]
                       (mkImpl oprop0 desc0)
                       nullRange
    DataHasValue _ _ -> fail "DataHasValue handling nyi"
    DataCardinality _ -> fail "DataCardinality handling nyi"
