{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  Comorphism from OWL2 to Common Logic
Copyright   :  (c) Francisc-Nicolae Bungiu
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.bungiu@jacobs-university.de
Stability   :  provisional
Portability :  non-portable (via Logic.Logic)

a comorphism from OWL2 to CommonLogic
-}

module OWL2.OWL22CommonLogic (OWL22CommonLogic (..)) where

import Logic.Logic as Logic
import Logic.Comorphism
import qualified Common.AS_Annotation as CommonAnno
import Common.Result
import Control.Monad
import Data.Char
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.Map as Map

-- OWL2 = domain
import OWL2.Logic_OWL2
import OWL2.AS
import OWL2.MS
import OWL2.ProfilesAndSublogics
import OWL2.Morphism
import OWL2.Symbols
import qualified OWL2.Sign as OS
-- CommonLogic = codomain
import CommonLogic.Logic_CommonLogic
import Common.Id as Id
import CommonLogic.AS_CommonLogic
import CommonLogic.Sign
import CommonLogic.Symbol
import qualified CommonLogic.Morphism as CLM
import qualified CommonLogic.Sublogic as ClSl

import Common.ProofTree

data OWL22CommonLogic = OWL22CommonLogic deriving Show

instance Language OWL22CommonLogic

instance Comorphism
    OWL22CommonLogic        -- comorphism
    OWL2                    -- lid domain
    ProfSub                  -- sublogics domain
    OntologyDocument        -- Basic spec domain
    Axiom                   -- sentence domain
    SymbItems               -- symbol items domain
    SymbMapItems            -- symbol map items domain
    OS.Sign                 -- signature domain
    OWLMorphism             -- morphism domain
    Entity                  -- symbol domain
    RawSymb                 -- rawsymbol domain
    ProofTree               -- proof tree codomain
    CommonLogic             -- lid codomain
    ClSl.CommonLogicSL      -- sublogics codomain
    BASIC_SPEC              -- Basic spec codomain
    TEXT                    -- sentence codomain
    NAME                    -- symbol items codomain
    SYMB_MAP_ITEMS          -- symbol map items codomain
    Sign                    -- signature codomain
    CLM.Morphism            -- morphism codomain
    Symbol                  -- symbol codomain
    Symbol                  -- rawsymbol codomain
    ProofTree               -- proof tree domain
    where
      sourceLogic OWL22CommonLogic = OWL2
      sourceSublogic OWL22CommonLogic = topS
      targetLogic OWL22CommonLogic = CommonLogic
      mapSublogic OWL22CommonLogic _ = Just ClSl.top
      map_theory OWL22CommonLogic = mapTheory
      map_morphism OWL22CommonLogic = mapMorphism
      map_symbol OWL22CommonLogic _ = mapSymbol
      isInclusionComorphism OWL22CommonLogic = True
      has_model_expansion OWL22CommonLogic = True

-- | Mapping of OWL morphisms to CommonLogic morphisms
mapMorphism :: OWLMorphism -> Result CLM.Morphism
mapMorphism oMor =
  do
    dm <- mapSign $ osource oMor
    cd <- mapSign $ otarget oMor
    mapp <- mapMap $ mmaps oMor
    return (CLM.mkMorphism dm cd mapp)

data VarOrIndi = OVar Int | OIndi IRI

hetsPrefix :: String
hetsPrefix = ""

mapMap :: Map.Map Entity IRI -> Result (Map.Map Id Id)
mapMap m =
  return $ Map.map uriToId $ Map.mapKeys entityToId m

mapSymbol :: Entity -> Set.Set Symbol
mapSymbol (Entity _ iri) = Set.singleton $ idToRaw $ uriToId iri

mapSign :: OS.Sign             -- ^ OWL2 signature
        -> Result Sign         -- ^ CommonLogic signature
mapSign sig =
  let conc = Set.unions [ OS.concepts sig
                        , OS.datatypes sig
                        , OS.objectProperties sig
                        , OS.dataProperties sig
                        , OS.annotationRoles sig
                        , OS.individuals sig ]
      itms = Set.map uriToId conc
  in return emptySig { items = itms }


mapTheory :: (OS.Sign, [CommonAnno.Named Axiom])
             -> Result (Sign, [CommonAnno.Named TEXT])
mapTheory (owlSig, owlSens) =
  do
    cSig <- mapSign owlSig
    (cSensI, nSig) <- foldM (\ (x, y) z ->
              do
                (sen, sig) <- mapSentence y z
                return (sen ++ x, unite sig y)
                ) ([], cSig) owlSens
    return (nSig, cSensI)


-- | mapping of OWL to CommonLogic_DL formulae
mapSentence :: Sign                             -- ^ CommonLogic Signature
  -> CommonAnno.Named Axiom                     -- ^ OWL2 Sentence
  -> Result ([CommonAnno.Named TEXT], Sign)     -- ^ CommonLogic TEXT
mapSentence cSig inSen = do
            (outAx, outSig) <- mapAxioms cSig $ CommonAnno.sentence inSen
            return (map (flip CommonAnno.mapNamed inSen . const) outAx, outSig)

-- | Mapping of Axioms
mapAxioms :: Sign                       -- ^ CommonLogic Signature
          -> Axiom                      -- ^ OWL2 Axiom
          -> Result ([TEXT], Sign)      -- ^ CommonLogic TEXT
mapAxioms cSig ax =
  case ax of
    PlainAxiom ex fb ->
      case fb of
        ListFrameBit rel lfb ->
          mapListFrameBit cSig ex rel lfb
        AnnFrameBit _anno afb ->
          mapAnnFrameBit cSig ex afb


mkQuants :: QUANT_SENT -> SENTENCE
mkQuants qs = Quant_sent qs nullRange

mkBools :: BOOL_SENT -> SENTENCE
mkBools bs = Bool_sent bs nullRange

mkAtoms :: ATOM -> SENTENCE
mkAtoms as = Atom_sent as nullRange

mkUnivQ :: [NAME_OR_SEQMARK] -> SENTENCE -> QUANT_SENT
mkUnivQ = Universal

mkExist :: [NAME_OR_SEQMARK] -> SENTENCE -> QUANT_SENT
mkExist = Existential

cnjct :: [SENTENCE] -> BOOL_SENT
cnjct = Conjunction

dsjct :: [SENTENCE] -> BOOL_SENT
dsjct = Disjunction

mkNeg :: SENTENCE -> BOOL_SENT
mkNeg = Negation

mkImpl :: SENTENCE -> SENTENCE -> BOOL_SENT
mkImpl = Implication

mkBicnd :: SENTENCE -> SENTENCE -> BOOL_SENT
mkBicnd = Biconditional

mkNAME :: Int -> NAME_OR_SEQMARK
mkNAME n = Name (mkNName n)

mkNTERM :: Int -> TERM
mkNTERM n = Name_term (mkNName n)

mkEq :: TERM -> TERM -> ATOM
mkEq = Equation


-- | Mapping of ListFrameBit
mapListFrameBit :: Sign
                -> Extended
                -> Maybe Relation
                -> ListFrameBit
                -> Result ([TEXT], Sign)
mapListFrameBit cSig ex rel lfb = case lfb of
    AnnotationBit _a -> return ([], cSig)
    ExpressionBit cls ->
      case ex of
          Misc _ -> return ([], cSig)
          SimpleEntity (Entity ty iri) ->
            case ty of
              NamedIndividual | rel == Just Types ->
                do
                  inD <- mapIndivIRI cSig iri
                  ls <- mapM (\ (_, c) -> mapDescription
                                      cSig c (OIndi iri) 1 ) cls
                  let ocls = map fst ls
                      dSig = map snd ls
                      map2nd = map snd cls
                  case map2nd of
                         [Expression _] ->
                                return (msen2Txt ocls, uniteL dSig)
                         _ ->
                            return (msen2Txt $ map (mkQuants .
                                          mkUnivQ [mkNAME 1] .
                                          mkBools . mkImpl (mkAtoms
                                   (mkEq (mkNTERM 1) inD))) ocls, cSig)

              DataProperty | rel == (Just $ DRRelation ADomain) ->
                do
                  ls <- mapM (\ (_, c) -> mapDescription
                                            cSig c (OIndi iri) 1 ) cls
                  oEx <- mapDataProp cSig iri (OVar 1) (OVar 2)
                  let odes = map fst ls
                      dSig = map snd ls
                  return (msen2Txt $ map (mkQuants .
                                          mkUnivQ [mkNAME 1] .
                                          mkQuants . mkExist [mkNAME 2] .
                                          mkBools . mkImpl oEx) odes
                         , uniteL dSig)
              _ -> return ([], cSig)

          ObjectEntity oe ->
            case rel of
              Nothing -> return ([], cSig)
              Just re ->
                case re of
                  DRRelation r -> do
                    tobjP <- mapObjProp cSig oe (OVar 1) (OVar 2)
                    tdsc <- mapM (\ (_, c) -> mapDescription cSig c (
                      case r of
                        ADomain -> OVar 1
                        ARange -> OVar 2)
                      (case r of
                        ADomain -> 1
                        ARange -> 2)) cls
                    let vars = case r of
                                 ADomain -> (1, 2)
                                 ARange -> (2, 1)
                        mapfst = map fst tdsc
                        dSig = map snd tdsc
                    return (msen2Txt $ map (mkQuants .
                                    mkUnivQ [mkNAME (fst vars)] .
                                    mkQuants . mkExist [mkNAME (snd vars)] .
                                    mkBools . mkImpl tobjP) mapfst, uniteL dSig)

                  _ -> fail "ObjectEntity Relation nyi"
          ClassEntity ce -> do
            let map2nd = map snd cls
            case rel of
              Nothing -> return ([], cSig)
              Just r -> case r of
                EDRelation re ->
                  do
                    (decrsS, dSig) <- mapDescriptionListP cSig 1
                      $ comPairsaux ce map2nd
                    let
                        decrsP = case re of
                              Equivalent ->
                                  map (\ (x, y) -> mkBools (mkBicnd x y)) decrsS
                              Disjoint ->
                                  map (\ (x, y) -> mkBools (mkNeg
                                              (mkBools (cnjct [x, y])))) decrsS
                        snt = if length decrsP == 1 then
                                  head decrsP
                                else
                                  mkBools (cnjct decrsP)
                    return (msen2Txt [mkQuants (mkUnivQ
                              [mkNAME 1]
                             snt)], dSig)

                SubClass ->
                  do
                    (domT, dSig) <- mapDescription cSig ce (OVar 1) 1
                    ls <- mapM (\ cd -> mapDescription cSig cd (OVar 1) 1)
                                        map2nd
                    let
                      codT = map fst ls
                      eSig = map snd ls
                    rSig <- sigUnion cSig (unite dSig (uniteL eSig))
                    return (msen2Txt $ map (mkQuants . mkUnivQ [mkNAME 1] .
                                         mkBools . mkImpl domT) codT, rSig)
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
          pairs <- mapComObjectPropsList cSig map2nd (OVar 1) (OVar 2)
          let sntLst = case ed of
                         Equivalent ->
                           map (\ (x, y) -> mkBools (mkBicnd x y)) pairs
                         Disjoint ->
                           map (\ (x, y) -> mkBools (mkNeg
                                            (mkBools (cnjct [x, y])))) pairs
              snt = if length sntLst == 1 then
                                  head sntLst
                                else
                                  mkBools (cnjct sntLst)
          return (msen2Txt [mkQuants (mkUnivQ
                              [mkNAME 1, mkNAME 2]
                             snt)], cSig)

        SubPropertyOf | isJ -> do
                  os <- mapM (\ (o1, o2) -> mapSubObjProp cSig o1 o2 3)
                    $ comPairsaux ob map2nd
                  return (msen2Txt os, cSig)

        InverseOf | isJ ->
          do
             os1 <- mapM (\ o1 -> mapObjProp cSig o1 (OVar 1) (OVar 2)) map2nd
             o2 <- mapObjProp cSig ob (OVar 2) (OVar 1)
             return (msen2Txt $ map (\ cd -> mkQuants (mkUnivQ
                             [mkNAME 1, mkNAME 2]
                             (mkBools (mkBicnd cd o2)))) os1, cSig)

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
          os1 <- mapM (\ o1 -> mapDataProp cSig o1 (OVar 1) (OVar 2)) map2nd
          o2 <- mapDataProp cSig ob (OVar 1) (OVar 2)
          return (msen2Txt $ map (\ cd -> mkQuants (mkUnivQ
                    [mkNAME 1, mkNAME 2]
                    (mkBools (mkImpl cd o2)))) os1, cSig)

        EDRelation ed -> do
          pairs <- mapComDataPropsList cSig map2nd (OVar 1) (OVar 2)
          let sntLst = case ed of
                         Equivalent ->
                            map (\ (x, y) ->
                              mkBools (mkBicnd x y)) pairs
                         Disjoint ->
                            map (\ (x, y) ->
                              mkBools (mkNeg (mkBools (cnjct [x, y])))) pairs
              snt = if length sntLst == 1 then
                                 head sntLst
                               else
                                 mkBools (cnjct sntLst)
          return (msen2Txt [mkQuants (mkUnivQ
                             [mkNAME 1, mkNAME 2]
                           snt)], cSig)

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
                return (msen2Txt fs, cSig)
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
                                    oEx <- mapDataProp cSig iri
                                             (OVar 1) (OVar 2)
                                    ls <- mapM (\ (_, c) ->
                                            mapDataRange cSig c (OVar 2)) dpr
                                    let dSig = map snd ls
                                        odes = map fst ls
                                    return (msen2Txt $ map (mkQuants .
                                                    mkUnivQ [mkNAME 1] .
                                                    mkQuants .
                                                    mkExist [mkNAME 2] .
                                                    mkBools . mkImpl oEx)
                                               odes
                                           , uniteL dSig)
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
                      oPropH <- mapObjProp cSig obe (OIndi siri) (OIndi ind)
                      let oProp = case posneg of
                                      Positive -> oPropH
                                      Negative -> mkBools (mkNeg oPropH)
                      return (msen2Txt [oProp], cSig)

              _ -> fail "ObjectPropertyFactsFacts Entity fail"
          [DataPropertyFact posneg dpe lit] ->
            case ex of
              SimpleEntity (Entity ty iri) ->
                case ty of
                  NamedIndividual ->
                    do
                      inS <- mapIndivIRI cSig iri
                      inT <- mapConstant cSig lit
                      nm <- uriToTokM dpe
                      let dPropH = mkAtoms (Atom
                                           (Name_term nm)
                                           [Term_seq inS, Term_seq inT])
                          dProp = case posneg of
                                        Positive -> dPropH
                                        Negative -> mkBools (mkNeg dPropH)
                      return (msen2Txt [dProp], cSig)
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
                so1 <- mapObjProp cSig ope (OVar 1) (OVar 2)
                so2 <- mapObjProp cSig ope (OVar 1) (OVar 3)
                return (msen2Txt [mkQuants (mkUnivQ
                                   [mkNAME 1, mkNAME 2, mkNAME 3]
                                   (mkBools (mkImpl (mkBools (cnjct [so1, so2]))
                                   (mkAtoms (mkEq
                                   (mkNTERM 2) (mkNTERM 3))))))], cSig)
            [InverseFunctional] ->
               do
                 so1 <- mapObjProp cSig ope (OVar 1) (OVar 3)
                 so2 <- mapObjProp cSig ope (OVar 2) (OVar 3)
                 return (msen2Txt [mkQuants (mkUnivQ
                                    [mkNAME 1, mkNAME 2, mkNAME 2]
                                    (mkBools (mkImpl (mkBools
                                    (cnjct [so1, so2]))
                                    (mkAtoms (mkEq
                                    (mkNTERM 1) (mkNTERM 2))))))], cSig)
            [Reflexive] ->
              do
                so <- mapObjProp cSig ope (OVar 1) (OVar 1)
                return (msen2Txt [mkQuants (mkUnivQ
                                   [mkNAME 1] so)], cSig)
            [Irreflexive] ->
              do
                so <- mapObjProp cSig ope (OVar 1) (OVar 1)
                return (msen2Txt [mkQuants (mkUnivQ
                                  [mkNAME 1]
                                  (mkBools (mkNeg so)))], cSig)
            [Symmetric] ->
              do
                 so1 <- mapObjProp cSig ope (OVar 1) (OVar 2)
                 so2 <- mapObjProp cSig ope (OVar 2) (OVar 1)
                 return (msen2Txt [mkQuants (mkUnivQ
                          [mkNAME 1, mkNAME 2]
                          (mkBools (mkImpl so1 so2)))], cSig)
            [Asymmetric] ->
              do
                so1 <- mapObjProp cSig ope (OVar 1) (OVar 2)
                so2 <- mapObjProp cSig ope (OVar 2) (OVar 1)
                return (msen2Txt [mkQuants (mkUnivQ
                                   [mkNAME 1, mkNAME 2]
                                   (mkBools (mkImpl so1
                                     (mkBools (mkNeg so2)))))], cSig)
            [Antisymmetric] ->
              do
                so1 <- mapObjProp cSig ope (OVar 1) (OVar 2)
                so2 <- mapObjProp cSig ope (OVar 2) (OVar 1)
                return (msen2Txt [mkQuants (mkUnivQ
                                   [mkNAME 1, mkNAME 2]
                                  (mkBools (mkImpl
                                   (mkBools (cnjct [so1, so2]))
                                   (mkAtoms (mkEq (mkNTERM 1) (mkNTERM 2))
                                  ))))], cSig)
            [Transitive] ->
              do
                so1 <- mapObjProp cSig ope (OVar 1) (OVar 2)
                so2 <- mapObjProp cSig ope (OVar 2) (OVar 3)
                so3 <- mapObjProp cSig ope (OVar 1) (OVar 3)
                return (msen2Txt [mkQuants (mkUnivQ
                             [mkNAME 1, mkNAME 2, mkNAME 3]
                             (mkBools (mkImpl
                                (mkBools (cnjct [so1, so2]))
                                so3
                             )))], cSig)
            _ -> fail "ObjectCharacteristics Character fail"
        _ -> fail "ObjectCharacteristics Entity fail"


-- | Mapping of AnnFrameBit
mapAnnFrameBit :: Sign
               -> Extended
               -> AnnFrameBit
               -> Result ([TEXT], Sign)
mapAnnFrameBit cSig ex afb =
  case afb of
    AnnotationFrameBit _ -> return ([], cSig)
    DataFunctional ->
      case ex of
        SimpleEntity (Entity ty iri) ->
          case ty of
            DataProperty ->
                do
                  so1 <- mapDataProp cSig iri (OVar 1) (OVar 2)
                  so2 <- mapDataProp cSig iri (OVar 1) (OVar 3)
                  return (msen2Txt [mkQuants (mkUnivQ
                                      [mkNAME 1, mkNAME 2, mkNAME 3]
                                     (mkBools (mkImpl
                                         (mkBools (cnjct [so1, so2]))
                                         (mkAtoms (mkEq
                                            (mkNTERM 2)
                                            (mkNTERM 3)))
                          )))], cSig)
            _ -> fail "DataFunctional EntityType fail"
        _ -> fail "DataFunctional Extend fail"
    DatatypeBit dt ->
      case ex of
        SimpleEntity (Entity ty iri) ->
          case ty of
            Datatype ->         
              do
                (odes, dSig) <- mapDataRange cSig dt (OVar 2)
                dtb <- mapDataProp cSig iri (OVar 1) (OVar 2)
                let res = [mkQuants (mkUnivQ
                            [mkNAME 1, mkNAME 2]
                             (mkBools (mkBicnd
                                dtb
                                odes)
                          ))]
                return (msen2Txt res, dSig)
            _ -> fail "DatatypeBit EntityType fail"
        _ -> fail "DatatypeBit Extend fail"
    ClassDisjointUnion clsl ->
      case ex of
        SimpleEntity (Entity ty iri) ->
          case ty of
            Class ->
                 do
                    (decrs, dSig) <- mapDescriptionList cSig 1 clsl
                    (decrsS, pSig) <- mapDescriptionListP cSig 1 $
                                        comPairs clsl clsl
                    let decrsP = unzip decrsS
                    mcls <- mapClassIRI cSig iri (mkNName 1)
                    return (msen2Txt [mkQuants (mkUnivQ
                              [mkNAME 1]
                               (mkBools (mkBicnd
                                 mcls (
                                mkBools (cnjct
                                [mkBools (dsjct decrs),
                                 mkBools (mkNeg (mkBools
                                 (cnjct (uncurry (++) decrsP
                            ))))])))))], unite dSig pSig)
            _ -> fail "ClassDisjointUnion EntityType fail"
        _ -> fail "ClassDisjointUnion Extend fail"
    ClassHasKey _obpe _dpe -> return ([], cSig)
    ObjectSubPropertyChain oplst ->
      do
        os <- mapM (\ cd -> mapSubObjPropChain cSig afb cd 3) oplst
        return (msen2Txt os, cSig)


senToText :: SENTENCE -> TEXT
senToText s = Text [Sentence s] nullRange

msen2Txt :: [SENTENCE] -> [TEXT]
msen2Txt = map senToText

-- | mapping of individual list
mapComIndivList :: Sign
                -> SameOrDifferent
                -> Maybe Individual
                -> [Individual]
                -> Result [SENTENCE]
mapComIndivList cSig sod mol inds = do
  fs <- mapM (mapIndivIRI cSig) inds
  _tps <- case mol of
    Nothing -> return $ comPairs fs fs
    Just ol -> do
      f <- mapIndivIRI cSig ol
      return $ comPairsaux f fs
  let inDL = comPairs fs fs
      sntLst = (map (\ (x, y) -> case sod of
                                   Same -> mkAtoms (mkEq x y)
                                   Different -> mkBools
                                     (mkNeg (mkAtoms
                                       (mkEq x y)))) inDL)
  return [mkBools (cnjct sntLst)]

{- | Mapping along ObjectPropsList for creation of pairs for commutative
operations. -}
mapComObjectPropsList :: Sign                    -- ^ Signature
                      -> [ObjectPropertyExpression]
                      -> VarOrIndi                        -- ^ First variable
                      -> VarOrIndi                         -- ^ Last  variable
                      -> Result [(SENTENCE, SENTENCE)]
mapComObjectPropsList cSig props num1 num2 =
  mapM (\ (x, z) -> do
        l <- mapObjProp cSig x num1 num2
        r <- mapObjProp cSig z num1 num2
        return (l, r)
        ) $ comPairs props props

toIRILst :: EntityType
         -> Extended
         -> Maybe IRI

toIRILst ty ane = case ane of
  SimpleEntity (Entity ty2 iri) | ty == ty2 -> Just iri
  _ -> Nothing

-- | Extracts Id from Entities
entityToId :: Entity -> Id
entityToId e =
  case e of
       Entity _ urI -> uriToId urI

-- | mapping of data constants
mapConstant :: Sign
            -> Literal
            -> Result TERM
mapConstant _ c =
  do
    let cl = case c of
              Literal l _ -> l
    return $ Name_term (mkSimpleId cl)

-- | Mapping of a list of data constants only for mapDataRange
mapConstantList :: Sign
                -> [Literal]
                -> Result [TERM]
mapConstantList sig = mapM (mapConstant sig)

mapSubObjPropChain :: Sign
              -> AnnFrameBit
              -> ObjectPropertyExpression
              -> Int
              -> Result SENTENCE
mapSubObjPropChain cSig prop oP num1 =
    let num2 = num1 + 1
    in
    case prop of
           ObjectSubPropertyChain props ->
             do
                 let zprops = zip (tail props) [(num2 + 1) ..]
                     (_, vars) = unzip zprops
                 oProps <- mapM (\ (z, x, y) -> mapObjProp
                                  cSig z (OVar x) (OVar y)) $
                                  zip3 props ((num1 : vars) ++ [num2]) $
                                       tail ((num1 : vars) ++ [num2])
                 ooP <- mapObjProp cSig oP (OVar num1) (OVar num2)
                 let lst = [ mkNAME num1
                           , mkNAME num2]
                           ++ map mkNAME vars
                 return $ mkQuants (mkUnivQ
                            lst
                            (mkBools (mkImpl
                                (mkBools (cnjct oProps))
                                ooP)))
           _ -> fail "mapping of ObjectSubPropertyChain failed"

-- | Mapping of subobj properties
mapSubObjProp :: Sign
              -> ObjectPropertyExpression
              -> ObjectPropertyExpression
              -> Int
              -> Result SENTENCE
mapSubObjProp cSig prop oP num1 = do
  let num2 = num1 + 1
  l <- mapObjProp cSig prop (OVar num1) (OVar num2)
  r <- mapObjProp cSig oP (OVar num1) (OVar num2)
  return $ mkQuants (mkUnivQ
             [mkNAME num1, mkNAME num2]
             (mkBools (mkImpl l r)))

{- | Mapping along DataPropsList for creation of pairs for commutative
operations. -}
mapComDataPropsList :: Sign
                      -> [DataPropertyExpression]
                      -> VarOrIndi                   -- ^ First variable
                      -> VarOrIndi                   -- ^ Last  variable
                      -> Result [(SENTENCE, SENTENCE)]
mapComDataPropsList cSig props num1 num2 =
  mapM (\ (x, z) -> do
                  l <- mapDataProp cSig x num1 num2
                  r <- mapDataProp cSig z num1 num2
                  return (l, r)
             ) $ comPairs props props

-- | Mapping of data properties
mapDataProp :: Sign
            -> DataPropertyExpression
            -> VarOrIndi
            -> VarOrIndi
            -> Result SENTENCE
mapDataProp _ dP nO nD =
  do
    let
        l = Name_term (voiToTok nO)
        r = Name_term (voiToTok nD)
    ur <- uriToTokM dP
    return $ mkAtoms
             (Atom
              (Name_term ur)
              [Term_seq l, Term_seq r]
             )

mapDataPropI :: Sign
             -> VarOrIndi
             -> VarOrIndi
             -> DataPropertyExpression
             -> Result SENTENCE
mapDataPropI cSig nO nD dP =
        mapDataProp cSig dP nO nD

-- | Mapping of obj props
mapObjProp :: Sign
              -> ObjectPropertyExpression
              -> VarOrIndi
              -> VarOrIndi
              -> Result SENTENCE
mapObjProp cSig ob var1 var2 =
  case ob of
         ObjectProp u ->
            do
              let l = Name_term (voiToTok var1)
                  r = Name_term (voiToTok var2)
              ur <- uriToTokM u
              return $ mkAtoms
                        (Atom
                          (Name_term ur)
                          [Term_seq l, Term_seq r]
                        )

         ObjectInverseOf u ->
            mapObjProp cSig u var2 var1

-- | Mapping of Class IRIs
mapClassIRI :: Sign
            -> Class
            -> Token
            -> Result SENTENCE
mapClassIRI _ uril uid =
  do
    ur <- uriToTokM uril
    return $ mkAtoms
             (Atom
              (Name_term ur)
              [Term_seq (Name_term uid)]
             )

-- | Mapping of Individual IRIs
mapIndivIRI :: Sign
            -> Individual
            -> Result TERM
mapIndivIRI _ uriI =
  do
    ur <- uriToTokM uriI
    return $ Name_term ur

voiToTok :: VarOrIndi -> Token
voiToTok v = case v of
        OVar o -> mkNName o
        OIndi o -> uriToTok o

uriToTokM :: IRI -> Result Token
uriToTokM = return . uriToTok

-- | Extracts Token from IRI
uriToTok :: IRI -> Token
uriToTok urI = mkSimpleId $ showQN urI

-- | Extracts Id from IRI
uriToId :: IRI -> Id
uriToId = simpleIdToId . uriToTok

-- | Mapping of a list of descriptions
mapDescriptionList :: Sign
                      -> Int
                      -> [ClassExpression]
                      -> Result ([SENTENCE], Sign)
mapDescriptionList cSig n lst = -- (zip lst $ replicate (length lst) n)
  do
    (sens, lSig) <- (mapAndUnzipM ((\ w x y z ->
                       mapDescription w z x y) cSig (OVar n) n) lst)
    sig <- sigUnionL lSig
    return (sens, sig)

-- | Mapping of a list of pairs of descriptions
mapDescriptionListP :: Sign
                    -> Int
                    -> [(ClassExpression, ClassExpression)]
                    -> Result ([(SENTENCE, SENTENCE)], Sign)
mapDescriptionListP cSig n lst =
    do
      let (l, r) = unzip lst
      (llst, ssSig) <- mapDescriptionList cSig n l
      (rlst, tSig) <- mapDescriptionList cSig n r
      let olst = zip llst rlst
      return (olst, unite ssSig tSig)

-- | Build a name
mkNName :: Int -> Token
mkNName i = mkSimpleId $ hetsPrefix ++ mkNName_H i
    where
      mkNName_H k =
          case k of
            0 -> ""
            j -> mkNName_H (j `div` 26) ++ [chr (j `mod` 26 + 96)]

-- | Get all distinct pairs for commutative operations
comPairs :: [t] -> [t1] -> [(t, t1)]
comPairs [] [] = []
comPairs _ [] = []
comPairs [] _ = []
comPairs (a : as) (_ : bs) = zip (replicate (length bs) a) bs ++ comPairs as bs

comPairsaux :: t -> [t1] -> [(t, t1)]
comPairsaux a = map (\ b -> (a, b))

-- | mapping of Data Range
mapDataRange :: Sign
             -> DataRange                 -- ^ OWL2 DataRange
             -> VarOrIndi                 -- ^ Current Variablename
             -> Result (SENTENCE, Sign)   -- ^ CommonLogic SENTENCE, Signature
mapDataRange cSig rn inId =
  do
    let uid = Name_term (voiToTok inId)
    case rn of
         DataJunction _ _ -> error "nyi"
         DataComplementOf dr ->
          do
            (dc, sig) <- mapDataRange cSig dr inId
            return (mkBools (mkNeg dc), sig)
         DataOneOf cs ->
          do
            cl <- mapConstantList cSig cs
            dl <- mapM (\ x -> return $ mkAtoms (Atom x [Term_seq uid])) cl
            return (mkBools (dsjct dl), cSig)
         DataType dt rlst ->
           do
            let (sent, rSig) = (mkAtoms (Atom
                                (Name_term (uriToTok dt))
                                [Term_seq uid]
                               ), cSig)
            (sens, sigL) <- (mapAndUnzipM (mapFacet cSig uid) rlst)
            return (mkBools (cnjct (sent : sens)
                            ), uniteL (rSig : sigL))

-- | mapping of a tuple of ConstrainingFacet and RestictionValue
mapFacet :: Sign
         -> TERM
         -> (ConstrainingFacet, RestrictionValue)
         -> Result (SENTENCE, Sign)
mapFacet sig var (f, r) =
    do
      con <- mapConstant sig r
      return (mkAtoms
                (Atom
                  (Name_term (uriToTok f))
                  [ Term_seq con
                  , Term_seq var ]
                ) , unite sig (emptySig
                   {items = Set.fromList [stringToId (showQN f)]} ))

-- | mapping of OWL Descriptions
mapDescription :: Sign
               -> ClassExpression           -- ^ OWL2 ClassExpression
               -> VarOrIndi                 -- ^ Current Variablename
               -> Int                       -- ^ Alternative to current
               -> Result (SENTENCE, Sign)   -- ^ CommonLogic_DL Formula
mapDescription cSig des oVar aVar =
  let varN = case oVar of
        OVar v -> mkNName v
        OIndi i -> uriToTok i
      var = case oVar of
        OVar v -> v
        OIndi _ -> aVar
  in case des of
         Expression cl ->
           do
            rslt <- mapClassIRI cSig cl varN
            return (rslt, cSig)
         ObjectJunction jt desL ->
           do
             (desO, dSig) <- (mapAndUnzipM ((\ w x y z ->
                                mapDescription w z x y) cSig oVar aVar)
                              desL)
             return $ case jt of
                UnionOf -> (mkBools (dsjct desO), uniteL dSig)
                IntersectionOf -> (mkBools (cnjct desO), uniteL dSig)
         ObjectComplementOf descr ->
           do
             (desO, dSig) <- mapDescription cSig descr oVar aVar
             return (mkBools (mkNeg desO), dSig)
         ObjectOneOf indS ->
           do
             indO <- mapM (mapIndivIRI cSig) indS
             let forms = map ((\ x y -> mkAtoms (mkEq x y))
                                          (Name_term varN)) indO
             return (mkBools (dsjct forms), cSig)
         ObjectValuesFrom qt oprop descr ->
           do
             opropO <- mapObjProp cSig oprop (OVar var) (OVar (var + 1))
             (descO, dSig) <- mapDescription cSig descr
                                  (OVar (var + 1)) (aVar + 1)
             case qt of
               SomeValuesFrom ->
                      return (mkQuants (mkExist
                                   [mkNAME (var + 1)]
                                (mkBools (cnjct [opropO, descO]))
                               ), dSig)
               AllValuesFrom ->
                   return (mkQuants (mkUnivQ
                                [mkNAME (var + 1)]
                                (mkBools (mkImpl opropO descO))), dSig)
         ObjectHasSelf oprop ->
            do
              rslt <- mapObjProp cSig oprop oVar oVar
              return (rslt, cSig)
         ObjectHasValue oprop indiv ->
            do
             rslt <- mapObjProp cSig oprop oVar (OIndi indiv)
             return (rslt, cSig)
         ObjectCardinality c ->
          case c of
               Cardinality ct n oprop d
                        ->
                          do
                            let vlst = [(var + 1) .. (n + var)]
                                vLst = map OVar vlst
                                vlstM = [(var + 1) .. (n + var + 1)]
                                vLstM = map OVar vlstM
                            (dOut, sigL) <- (\ x -> case x of
                                  Nothing -> return ([], [])
                                  Just y ->
                                    mapAndUnzipM (uncurry (mapDescription
                                      cSig y)) (zip vLst vlst)
                                 ) d
                            let dlst = map (\ (x, y) ->
                                              mkBools (mkNeg
                                               (mkAtoms (mkEq
                                                (mkNTERM x)
                                                (mkNTERM y)
                                           )))) $ comPairs vlst vlst
                                dlstM = map (\ (x, y) ->
                                              mkAtoms (mkEq
                                                (mkNTERM x)
                                                (mkNTERM y)
                                            )) $ comPairs vlstM vlstM
                                qVars = map mkNAME vlst
                                qVarsM = map mkNAME vlstM
                            oProps <- mapM (mapObjProp cSig oprop (OVar var))
                                            vLst
                            oPropsM <- mapM (mapObjProp cSig oprop (OVar var))
                                             vLstM
                            let minLst = mkQuants (mkExist
                                           qVars
                                           (mkBools (cnjct
                                               (dlst ++ dOut ++ oProps))))
                            let maxLst = mkQuants (mkExist
                                           qVarsM
                                           (mkBools (mkImpl
                                             (mkBools (cnjct (oPropsM ++ dOut)))
                                             (mkBools (dsjct dlstM)))))
                            case ct of
                               MinCardinality -> return (minLst, cSig)
                               MaxCardinality -> return (maxLst, cSig)
                               ExactCardinality -> return
                                           (mkBools (cnjct [minLst, maxLst])
                                           , uniteL sigL)
         DataValuesFrom qt dpe dr ->
            do
              let varNN = mkNName (var + 1)
              (drSent, drSig) <- mapDataRange cSig dr (OVar var)
              senl <- mapM (mapDataPropI cSig (OVar var) (OVar (var + 1))) [dpe]
              let sent = mkBools (cnjct (drSent : senl))
              case qt of
                   AllValuesFrom ->
                    return (mkQuants (mkUnivQ [Name varNN]
                                       sent), drSig)
                   SomeValuesFrom ->
                    return (mkQuants (mkExist [Name varNN]
                                        sent), drSig)
         DataHasValue dpe c ->
           do
             let dpet = Name_term $ uriToTok dpe
             con <- mapConstant cSig c
             return (mkQuants (mkUnivQ [Name varN]
                        (mkAtoms (Atom dpet
                                  [ Term_seq (Name_term varN)
                                  , Term_seq con]
                      ))), cSig)
         DataCardinality c ->
             case c of
                  Cardinality ct n dpe dr
                    ->
                      do
                        let vlst = [(var + 1) .. (n + var)]
                            vLst = map OVar vlst
                            vlstM = [(var + 1) .. (n + var + 1)]
                            vLstM = map OVar vlstM
                        (dOut, sigL) <- ( \ x -> case x of
                              Nothing -> return ([], [])
                              Just y ->
                                mapAndUnzipM (mapDataRange cSig y) vLst
                             ) dr
                        let dlst = map ( \ (x, y) -> mkBools (mkNeg
                                          (mkAtoms (mkEq
                                                (mkNTERM x)
                                                (mkNTERM y)))
                                          )) $ comPairs vlst vlst
                            dlstM = map ( \ (x, y) -> mkAtoms (mkEq
                                          (mkNTERM x) (mkNTERM y)
                                          )) $ comPairs vlstM vlstM
                            qVars = map mkNAME vlst
                            qVarsM = map mkNAME vlstM
                        dProps <- mapM ( mapDataProp cSig dpe (OVar var)) vLst
                        dPropsM <- mapM (mapDataProp cSig dpe (OVar var)) vLstM
                        let minLst = mkQuants (mkExist qVars
                                       (mkBools (cnjct
                                            (dlst ++ dOut ++ dProps))))
                        let maxLst = mkQuants (mkUnivQ
                                       qVarsM
                                       (mkBools (mkImpl
                                         (mkBools (cnjct (dPropsM ++ dOut)))
                                         (mkBools (dsjct dlstM)))))
                        case ct of
                            MinCardinality -> return (minLst, cSig)
                            MaxCardinality -> return (maxLst, cSig)
                            ExactCardinality -> return (mkBools (
                                                    cnjct [minLst, maxLst])
                                                    , uniteL sigL)
