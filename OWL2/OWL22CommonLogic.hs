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

module OWL2.OWL22CommonLogic (OWL22CommonLogic(..)) where

import Logic.Logic as Logic
import Logic.Comorphism
import qualified Common.AS_Annotation as CommonAnno
import Common.Result
import Common.Id
import Control.Monad
import Data.Char
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.Map as Map

-- OWL = domain
import OWL2.Logic_OWL2
import OWL2.AS
import OWL2.MS
import OWL2.Sublogic
import OWL2.Morphism
import OWL2.Symbols
import OWL2.Keywords
import qualified OWL2.Sign as OS
-- CommonLogic = codomain
import CommonLogic.Logic_CommonLogic
import Common.Id as Id
import CommonLogic.AS_CommonLogic
import CommonLogic.Sign
import CommonLogic.Symbol
import qualified CommonLogic.Morphism as CLM

import Common.ProofTree

data OWL22CommonLogic = OWL22CommonLogic deriving Show

instance Language OWL22CommonLogic

instance Comorphism
    OWL22CommonLogic        -- comorphism
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
    CommonLogic            -- lid codomain
    ()--CommonLogic_Sublogics  -- sublogics codomain
    BASIC_SPEC   -- Basic spec codomain
    SENTENCE     -- sentence codomain
    NAME      -- symbol items codomain
    SYMB_MAP_ITEMS  -- symbol map items codomain
    Sign        -- signature codomain
    CLM.Morphism         -- morphism codomain
    Symbol          -- symbol codomain
    Symbol       -- rawsymbol codomain
    ProofTree       -- proof tree domain
    where
      sourceLogic OWL22CommonLogic    = OWL2
      sourceSublogic OWL22CommonLogic = sl_top
      targetLogic OWL22CommonLogic    = CommonLogic
      mapSublogic OWL22CommonLogic _  = Just $ ()
      map_theory OWL22CommonLogic     = mapTheory
      map_morphism OWL22CommonLogic   = mapMorphism
      isInclusionComorphism OWL22CommonLogic = True
      has_model_expansion OWL22CommonLogic = True

-- | Mapping of OWL morphisms to CommonLogic morphisms
mapMorphism :: OWLMorphism -> Result CLM.Morphism
mapMorphism oMor =
  do
    dm <- mapSign $ osource oMor
    cd <- mapSign $ otarget oMor
    mapp <- mapMap $ mmaps oMor
    return  (CLM.mkMorphism dm cd mapp)

data VarOrIndi = OVar Int | OIndi IRI

hetsPrefix :: String
hetsPrefix = ""

mapMap :: Map.Map Entity IRI -> Result (Map.Map Id Id)
mapMap m =
  return $ Map.map uriToId $ Map.mapKeys entityToId m

mapSign :: OS.Sign                 -- ^ OWL signature
        -> Result Sign         -- ^ CommonLogic signature
mapSign sig =
  let conc = Set.unions [ (OS.concepts sig)
                        , (OS.datatypes sig)
                        , (OS.objectProperties sig)
                        , (OS.dataProperties sig)
                        , (OS.annotationRoles sig)
                        , (OS.individuals sig) ]
      itms = Set.map uriToId conc
  in return emptySig { items = itms }


mapTheory :: (OS.Sign, [CommonAnno.Named Axiom])
             -> Result (Sign, [CommonAnno.Named SENTENCE])
mapTheory (owlSig, owlSens) =
  do
    cSig <- mapSign owlSig
    (cSensI, nSig) <- foldM (\ (x,y) z ->
              do
                (sen, sig) <- mapSentence y z
                return (sen ++ x, unite sig y)
                ) ([], cSig) owlSens
    return (nSig, cSensI)


-- | mapping of OWL to CommonLogic_DL formulae
mapSentence :: Sign                           -- ^ CommonLogic Signature
  -> CommonAnno.Named Axiom                   -- ^ OWL2 Sentence
  -> Result ([CommonAnno.Named SENTENCE], Sign) -- ^ CommonLogic SENTENCE
mapSentence cSig inSen = do
            (outAx, outSig) <- mapAxiom cSig $ CommonAnno.sentence inSen
            return (map (flip CommonAnno.mapNamed inSen . const) outAx, outSig)

-- | Mapping of Axioms
mapAxiom :: Sign                             -- ^ CommonLogic Signature
         -> Axiom                                -- ^ OWL2 Axiom
         -> Result ([SENTENCE], Sign) -- ^ CommonLogic SENTENCE
mapAxiom cSig _ax = return ([], cSig)
{-
mapAxiom cSig ax =
    let
        a = 1
        b = 2
        c = 3
    in
      case ax of
        PlainAxiom _ pAx ->
            case pAx of
              SubClassOf sub super ->
                  do
                    (domT, dSig) <- mapDescription cSig sub   (OVar a) a
                    (codT, eSig) <- mapDescription cSig super (OVar a) a
                    rSig <- sigUnion cSig (unite dSig eSig)
                    return (Just $ Quant_sent (Universal
                               [Name (mkNName a)]
                               (Bool_sent (Implication
                                domT
                                codT)
                                nullRange)) nullRange, rSig)
              EquivOrDisjointClasses eD dS ->
                  do
                    (decrsS, dSig) <- mapDescriptionListP cSig a $ comPairs dS dS
                    let decrsP = case eD of
                              Equivalent ->
                                  map (\(x,y) -> Bool_sent (Biconditional x y) nullRange)
                                      decrsS
                              Disjoint   ->
                                  map (\(x,y) -> Bool_sent (Negation
                                       (Bool_sent (Conjunction [x,y]) nullRange)) nullRange)
                                       decrsS
                        snt = if (length decrsP == 1) then
                                  head decrsP
                                else
                                  Bool_sent (Conjunction decrsP) nullRange
                    return (Just $ Quant_sent (Universal
                              [Name (mkNName a)]
                               snt) nullRange, dSig)
              DisjointUnion cls sD ->
                  do
                    (decrs, dSig)  <- mapDescriptionList cSig a sD
                    (decrsS, pSig) <- mapDescriptionListP cSig a $ comPairs sD sD
                    let decrsP = unzip decrsS
                    mcls <- mapClassIRI cSig cls (mkNName a)
                    return (Just $ Quant_sent (Universal
                              [Name (mkNName a)]
                               (
                                Bool_sent (Biconditional
                                  mcls                 -- The class
                                (                      -- The rest
                                  Bool_sent (Conjunction
                                  [
                                   (Bool_sent (Disjunction decrs) nullRange)
                                  ,(Bool_sent (Negation
                                     (
                                      Bool_sent (Conjunction
                                      ((fst decrsP) ++ (snd decrsP))) nullRange
                                     )
                                    ) nullRange)
                                  ]) nullRange
                                )
                               ) nullRange
                               )
                               ) nullRange, unite dSig pSig)
              SubObjectPropertyOf ch op ->
                  do
                    os <- mapSubObjProp cSig ch op c
                    return (Just os, cSig)
              EquivOrDisjointObjectProperties disOrEq oExLst ->
                  do
                    pairs <- mapComObjectPropsList cSig oExLst (OVar a) (OVar b)
                    let sntLst = case disOrEq of
                                   Equivalent ->
                                       map (\(x,y) ->
                                                Bool_sent (Biconditional x y) nullRange) pairs
                                   Disjoint   ->
                                       map (\(x,y) ->
                                                (Bool_sent (Negation
                                                 (Bool_sent (Conjunction [x,y]) nullRange)) nullRange
                                                )
                                           ) pairs
                        snt = if (length sntLst == 1) then
                                  head sntLst
                                else
                                  Bool_sent (Conjunction
                                    sntLst) nullRange
                    return (Just $ Quant_sent (Universal
                              [ Name (mkNName a)
                              , Name (mkNName b)]
                               snt) nullRange, cSig)
              ObjectPropertyDomainOrRange domOrRn objP descr ->
                        do
                          tobjP <- mapObjProp cSig objP (OVar a) (OVar b)
                          (tdsc, dSig)  <- uncurry (mapDescription cSig descr) $
                                   case domOrRn of
                                     ObjDomain -> (OVar a, a)
                                     ObjRange  -> (OVar b, b)
                          let vars = case domOrRn of
                                       ObjDomain -> (mkNName a, mkNName b)
                                       ObjRange  -> (mkNName b, mkNName a)
                          return (Just $ Quant_sent (Universal
                                     [Name (fst vars)]
                                     (
                                      Quant_sent (Existential
                                         [Name (snd vars)]
                                         (
                                          Bool_sent (Implication
                                           tobjP
                                           tdsc
                                         ) nullRange))
                                      nullRange
                                     ))
                                     nullRange, dSig)
              InverseObjectProperties o1 o2 ->
                  do
                    so1 <- mapObjProp cSig o1 (OVar a) (OVar b)
                    so2 <- mapObjProp cSig o2 (OVar b) (OVar a)
                    return (Just $ Quant_sent (Universal
                             [Name (mkNName a)
                             ,Name (mkNName b)]
                             (
                             Bool_sent (
                              Biconditional
                              so1
                              so2
                             ) nullRange ))
                             nullRange, cSig)
              ObjectPropertyCharacter cha o ->
                  case cha of
                    Functional ->
                        do
                          so1 <- mapObjProp cSig o (OVar a) (OVar b)
                          so2 <- mapObjProp cSig o (OVar a) (OVar c)
                          return (Just $ Quant_sent (Universal
                                     [Name (mkNName a)
                                     ,Name (mkNName b)
                                     ,Name (mkNName c)
                                     ]
                                     (
                                      Bool_sent (Implication
                                      (
                                       Bool_sent (Conjunction [so1, so2]) nullRange
                                      )
                                      (
                                      Atom_sent
                                        (
                                         Equation
                                          (
                                            Name_term (mkNName b)
                                          )
                                          (
                                            Name_term (mkNName c)
                                          )
                                        )
                                        nullRange
                                      )
                                     ) nullRange))
                                     nullRange, cSig)
                    InverseFunctional ->
                        do
                          so1 <- mapObjProp cSig o (OVar a) (OVar c)
                          so2 <- mapObjProp cSig o (OVar b) (OVar c)
                          return (Just $ Quant_sent (Universal
                                     [Name (mkNName a)
                                     ,Name (mkNName b)
                                     ,Name (mkNName c)
                                     ]
                                     (
                                      Bool_sent (Implication
                                      (
                                       Bool_sent (Conjunction [so1, so2]) nullRange
                                      )
                                      (
                                       Atom_sent
                                       (
                                        Equation
                                        (
                                          Name_term (mkNName a)
                                        )
                                        (
                                          Name_term (mkNName b)
                                        )
                                       )
                                       nullRange
                                      )
                                     ) nullRange ))
                                     nullRange, cSig)
                    Reflexive  ->
                        do
                          so <- mapObjProp cSig o (OVar a) (OVar a)
                          return (Just $ Quant_sent (Universal
                                   [Name (mkNName a)]
                                    so)
                                    nullRange, cSig)
                    Irreflexive ->
                        do
                          so <- mapObjProp cSig o (OVar a) (OVar a)
                          return
                                 (Just $ Quant_sent (Universal
                                   [Name (mkNName a)]
                                   (Bool_sent (Negation so) nullRange))
                                   nullRange, cSig)
                    Symmetric ->
                        do
                          so1 <- mapObjProp cSig o (OVar a) (OVar b)
                          so2 <- mapObjProp cSig o (OVar b) (OVar a)
                          return
                           (Just $ Quant_sent (Universal
                               [Name (mkNName a)
                               ,Name (mkNName b)]
                               (
                                Bool_sent (Implication
                                so1
                                so2
                               ) nullRange))
                               nullRange, cSig)
                    Asymmetric ->
                        do
                          so1 <- mapObjProp cSig o (OVar a) (OVar b)
                          so2 <- mapObjProp cSig o (OVar b) (OVar a)
                          return
                           (Just $ Quant_sent (Universal
                               [Name (mkNName a)
                               ,Name (mkNName b)]
                               (
                                Bool_sent (Implication
                                so1
                                (Bool_sent (Negation so2) nullRange)
                               ) nullRange))
                               nullRange, cSig)
                    Antisymmetric ->
                        do
                          so1 <- mapObjProp cSig o (OVar a) (OVar b)
                          so2 <- mapObjProp cSig o (OVar b) (OVar a)
                          return
                           (Just $ Quant_sent (Universal
                               [Name (mkNName a)
                               ,Name (mkNName b)]
                               (
                                Bool_sent (Implication
                                 (Bool_sent (Conjunction [so1, so2]) nullRange)
                                 (
                                  Atom_sent
                                  (
                                    Equation
                                    (
                                      Name_term (mkNName a)
                                    )
                                    (
                                      Name_term (mkNName b)
                                    )
                                  )
                                  nullRange
                                 )
                               ) nullRange))
                               nullRange, cSig)
                    Transitive ->
                        do
                          so1 <- mapObjProp cSig o (OVar a) (OVar b)
                          so2 <- mapObjProp cSig o (OVar b) (OVar c)
                          so3 <- mapObjProp cSig o (OVar a) (OVar c)
                          return
                           (Just $ Quant_sent (Universal
                               [Name (mkNName a)
                               ,Name (mkNName b)
                               ,Name (mkNName c)]
                               (
                                Bool_sent (Implication
                                (
                                 Bool_sent (Conjunction [so1, so2]) nullRange
                                )
                                 so3
                               ) nullRange))
                               nullRange, cSig)
              SubDataPropertyOf subDP superDP ->
                  do
                    l <- mapDataProp cSig subDP (OVar a) (OVar b)
                    r <- mapDataProp cSig superDP  (OVar a) (OVar b)
                    return (Just $ Quant_sent (Universal
                               [ Name (mkNName a)
                               , Name (mkNName b)]
                               (
                                Bool_sent (Implication
                                l
                                r) nullRange)
                               )
                               nullRange, cSig)
              EquivOrDisjointDataProperties disOrEq dlst ->
                  do
                    pairs <- mapComDataPropsList cSig dlst (OVar a) (OVar b)
                    let sntLst = case disOrEq of
                                   Equivalent ->
                                       map (\(x,y) ->
                                                Bool_sent (Biconditional x y) nullRange) pairs
                                   Disjoint   ->
                                       map (\(x,y) ->
                                                (Bool_sent (Negation
                                                 (Bool_sent (Conjunction [x,y]) nullRange)
                                                ) nullRange )
                                           ) pairs
                        snt = if (length sntLst == 1) then
                                 head sntLst
                               else
                                 Bool_sent (Conjunction sntLst) nullRange
                    return (Just $ Quant_sent (Universal
                              [ Name (mkNName a)


                              , Name (mkNName b)]
                               snt)
                               nullRange, cSig)
              DataPropertyDomainOrRange domRn dpex ->
                        do
                          oEx <- mapDataProp cSig dpex (OVar a) (OVar b)
                          case domRn of
                            DataDomain mdom ->
                                do
                                  (odes, dSig) <- mapDescription cSig mdom (OVar a) a
                                  let vars = (mkNName a, mkNName b)
                                  return (Just $ Quant_sent (Universal
                                         [Name (fst vars)]
                                         (Quant_sent (Existential
                                         [Name (snd vars)]
                                         (Bool_sent (Implication oEx odes) nullRange))
                                         nullRange)) nullRange, dSig)
                            DataRange  rn  ->
                                do
                                  (odes, dSig) <- mapDataRange cSig rn (OVar b)
                                  let vars = (mkNName a, mkNName b)
                                  return (Just $ Quant_sent (Universal
                                         [Name (fst vars)]
                                         (Quant_sent (Existential
                                         [Name (snd vars)]
                                         (Bool_sent (Implication oEx odes) nullRange))
                                         nullRange)) nullRange, dSig)
              FunctionalDataProperty o ->
                        do
                          so1 <- mapDataProp cSig o (OVar a) (OVar b)
                          so2 <- mapDataProp cSig o (OVar a) (OVar c)
                          return (Just $ Quant_sent (Universal
                                     [Name (mkNName a)
                                     ,Name (mkNName b)
                                     ,Name (mkNName c)
                                     ]
                                     (
                                      Bool_sent (Implication
                                      (
                                       Bool_sent (Conjunction [so1, so2]) nullRange
                                      )
                                      (Atom_sent (
                                        Equation
                                        (
                                          Name_term (mkNName b)
                                        )
                                        (
                                          Name_term (mkNName c)
                                        )
                                      ) nullRange)
                                     ) nullRange))
                                    nullRange, cSig
                                   )
              SameOrDifferentIndividual sameOrDiff indis ->
                  do
                    inD <- mapM (mapIndivIRI cSig) indis
                    let inDL = comPairs inD inD
                        sntLst = (map (\ (x, y) -> case sameOrDiff of
                                   Same -> Atom_sent (Equation x y) nullRange
                                   Different -> Bool_sent (Negation
                                     (Atom_sent (Equation x y) nullRange)) nullRange
                                 ) inDL)
                    if (length sntLst == 1) then
                       return (Just $ head sntLst, cSig)
                      else
                        return (Just $ (Bool_sent (Conjunction sntLst
                             ) nullRange), cSig)
              ClassAssertion indi cls ->
                  do
                    inD  <- mapIndivIRI cSig indi
                    (ocls, dSig) <- mapDescription cSig cls (OIndi indi) a
                    case cls of
                         OWLClassDescription _ ->
                                return (Just $ ocls, dSig)
                         _ ->
                            return (Just $  Quant_sent (Universal
                              [Name (mkNName a)]
                              (
                              Bool_sent (
                               Implication
                               (Atom_sent (
                                Equation
                                  (Name_term (mkNName a))
                                   inD
                               ) nullRange)
                                ocls
                                ) nullRange )) nullRange , dSig)
              ObjectPropertyAssertion ass ->
                 case ass of
                    Assertion objProp posNeg sInd tInd ->
                      do
                        oPropH <- mapObjProp cSig objProp (OIndi sInd) (OIndi tInd)
                        let oProp = case posNeg of
                                      Positive -> oPropH
                                      Negative -> Bool_sent (Negation
                                                    oPropH)
                                                    nullRange
                        return (Just oProp, cSig)
              DataPropertyAssertion ass ->
                  case ass of
                    Assertion dPropExp posNeg sourceInd targetInd ->
                        do
                          inS <- mapIndivIRI cSig sourceInd
                          inT <- mapConstant cSig targetInd
                          nm <- uriToTokM dPropExp
                          let dPropH = Atom_sent
                                            (
                                              Atom
                                              (Name_term nm)
                                              [ Term_seq inS, Term_seq inT]
                                            )
                                        nullRange
                              dProp = case posNeg of
                                        Positive -> dPropH
                                        Negative -> Bool_sent (Negation
                                                    dPropH) nullRange
                          return (Just $  dProp, cSig)
              Declaration _ -> return (Nothing, cSig)
        EntityAnno _  -> return (Nothing, cSig)


-}

mkQuants :: QUANT_SENT -> SENTENCE
mkQuants qs = Quant_sent qs nullRange

mkBools :: BOOL_SENT -> SENTENCE
mkBools bs = Bool_sent bs nullRange

mkAtoms :: ATOM -> SENTENCE
mkAtoms as = Atom_sent as nullRange

mkComms :: COMMENT -> SENTENCE -> SENTENCE
mkComms cmt sen = Comment_sent cmt sen nullRange

mkIrregs :: SENTENCE -> SENTENCE
mkIrregs sen = Irregular_sent sen nullRange

mkUnivQ :: [NAME_OR_SEQMARK] -> SENTENCE -> QUANT_SENT
mkUnivQ ls sen = Universal ls sen

mkExist :: [NAME_OR_SEQMARK] -> SENTENCE -> QUANT_SENT
mkExist ls sen = Existential ls sen

cnjct :: [SENTENCE] -> BOOL_SENT
cnjct ls = Conjunction ls

dsjct :: [SENTENCE] -> BOOL_SENT
dsjct ls = Disjunction ls

mkNeg :: SENTENCE -> BOOL_SENT
mkNeg sen = Negation sen

mkImpl :: SENTENCE -> SENTENCE -> BOOL_SENT
mkImpl sen1 sen2 = Implication sen1 sen2

mkBicnd :: SENTENCE -> SENTENCE -> BOOL_SENT
mkBicnd s1 s2 = Biconditional s1 s2

mkNAME :: Int -> NAME_OR_SEQMARK
mkNAME n = Name (mkNName n)

mkSEQ :: SEQ_MARK -> NAME_OR_SEQMARK
mkSEQ sq = SeqMark sq

mkNTERM :: Int -> TERM
mkNTERM n = Name_term (mkNName n)

mkEq :: TERM -> TERM -> ATOM
mkEq t1 t2 = Equation t1 t2


-- | Mapping of ListFrameBit
mapListFrameBit :: Sign
                -> Extended
                -> Maybe Relation
                -> ListFrameBit
                -> Result ([SENTENCE], Sign)
mapListFrameBit cSig ex rel lfb = case lfb of
    AnnotationBit _a -> return ([], cSig)
    ExpressionBit cls ->
      case ex of
          Misc _ -> return ([], cSig)
          SimpleEntity (Entity ty iri) ->
            case ty of
              NamedIndividual | rel == Just Types ->
                do
                  inD  <- mapIndivIRI cSig iri
                  ls <- mapM (\ (_, c) -> mapDescription cSig c (OIndi iri) 1 ) cls
                  let ocls = map fst ls
                      dSig = map snd ls
                      map2nd = map snd cls
                  return ([], cSig)
                  case map2nd of
                         [Expression _] -> 
                                return (ocls, uniteL dSig)
                         _ ->
                            return (map (\ cd ->
                              mkQuants (mkUnivQ
                                [mkNAME 1](mkBools
                                  (mkImpl 
                                    (mkAtoms (mkEq (mkNTERM 1) inD))
                                    cd))
                              )) ocls, cSig)

              DataProperty | rel == (Just $ DRRelation ADomain) ->
                do
                  ls <- mapM (\ (_, c) -> mapDescription cSig c (OIndi iri) 1 ) cls
                  oEx <- mapDataProp cSig iri (OVar 1) (OVar 2)
                  let odes = map fst ls
                      dSig = map snd ls
                  return (map (\cd -> mkQuants (mkUnivQ
                                         [mkNAME 1]
                                         (mkQuants (mkExist
                                         [mkNAME 2]
                                         (mkBools (mkImpl oEx cd))))
                                         )) odes, uniteL dSig)
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
                        ARange ->  2)) cls
                    let vars = case r of
                                 ADomain -> (1,2)
                                 ARange -> (2,1)
                        mapfst = map fst tdsc
                        dSig = map snd tdsc
                    return (map (\cd -> mkQuants (mkUnivQ
                                     [mkNAME (fst vars)]
                                     (mkQuants (mkExist
                                     [mkNAME (snd vars)]
                                     (mkBools (mkImpl tobjP cd))))
                                     )) mapfst, uniteL dSig)

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
                                  map (\(x,y) -> mkBools (mkBicnd x y)) decrsS
                              Disjoint   ->
                                  map (\(x,y) -> mkBools (mkNeg (mkBools (cnjct [x,y])))) decrsS
                        snt = if (length decrsP == 1) then
                                  head decrsP
                                else
                                  mkBools (cnjct decrsP)
                    return ([mkQuants (mkUnivQ
                              [mkNAME 1]
                             snt)], dSig)

                SubClass ->
                  do
                    (domT, dSig) <- mapDescription cSig ce (OVar 1) 1
                    ls <- mapM (\cd -> mapDescription cSig cd (OVar 1) 1) map2nd
                    let
                      codT = map fst ls
                      eSig = map snd ls
                    rSig <- sigUnion cSig (unite dSig (uniteL eSig))
                    return (map (\cd -> mkQuants (mkUnivQ
                               [mkNAME 1]
                               (mkBools (mkImpl domT cd))
                               )) codT, rSig)
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
                           map (\(x,y) -> mkBools (mkBicnd x y)) pairs
                         Disjoint   ->
                           map (\(x,y) -> mkBools (mkNeg (mkBools (cnjct [x,y])))) pairs
              snt = if (length sntLst == 1) then
                                  head sntLst
                                else
                                  mkBools (cnjct sntLst)
          return ([mkQuants (mkUnivQ
                              [mkNAME 1, mkNAME 2]
                             snt)], cSig)

        SubPropertyOf | isJ -> do
                  os <- mapM (\ (o1, o2) -> mapSubObjProp cSig o1 o2 3)
                    $ comPairsaux ob map2nd
                  return (os, cSig)

        InverseOf | isJ ->
          do
             os1 <- mapM (\ o1 -> mapObjProp cSig o1 (OVar 1) (OVar 2)) map2nd
             o2 <- mapObjProp cSig ob (OVar 2) (OVar 1)
             return (map (\cd -> mkQuants (mkUnivQ
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
          return (map (\ cd -> mkQuants (mkUnivQ
                    [mkNAME 1, mkNAME 2]
                    (mkBools (mkImpl cd o2)))) os1, cSig)

        EDRelation ed -> do
          pairs <- mapComDataPropsList cSig map2nd (OVar 1) (OVar 2)
          let sntLst = case ed of
                         Equivalent ->
                            map (\(x,y) ->
                              mkBools (mkBicnd x y)) pairs
                         Disjoint   ->
                            map (\(x,y) ->
                              mkBools (mkNeg (mkBools (cnjct [x,y])))) pairs
              snt = if (length sntLst == 1) then
                                 head sntLst
                               else
                                 mkBools (cnjct sntLst)                    
          return ([mkQuants (mkUnivQ
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
                                    oEx <- mapDataProp cSig iri (OVar 1) (OVar 2)
                                    ls <- mapM (\ (_, c) ->
                                                  mapDataRange cSig c (OVar 2)) dpr
                                    let dSig = map snd ls  
                                        odes = map fst ls
                                    return (map(\cd -> mkQuants (mkUnivQ
                                               [mkNAME 1]
                                               (mkQuants (mkExist
                                               [mkNAME 2]
                                                (mkBools (mkImpl oEx cd)))))) odes,
                                           uniteL dSig)
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
                      return ([oProp], cSig)
{-
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
                      return ([mkForall
                                [mkVarDecl (mkNName 1) thing,
                                 mkVarDecl (mkNName 2) thing]
                             (mkImpl (conjunct
                                        [mkStEq (toQualVar
                                          (mkVarDecl (mkNName 1) thing)) inS,
                                         mkStEq (toQualVar
                                          (mkVarDecl (mkNName 2) thing)) inT]
                             ) oProp)]
                             , cSig)
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
                return ([mkForall
                         [mkVarDecl (mkNName 1) thing,
                          mkVarDecl (mkNName 2) thing,
                          mkVarDecl (mkNName 3) thing]
                         (mkImpl
                           (conjunct [so1, so2])
                           (mkStEq
                              (toQualVar (mkVarDecl (mkNName 2) thing))
                              (toQualVar (mkVarDecl (mkNName 3) thing))
                           )
                       )], cSig)
            [InverseFunctional] ->
               do
                 so1 <- mapObjProp cSig ope 1 3
                 so2 <- mapObjProp cSig ope 2 3
                 return ([mkForall
                         [mkVarDecl (mkNName 1) thing,
                          mkVarDecl (mkNName 2) thing,
                          mkVarDecl (mkNName 3) thing]
                         (mkImpl
                           (conjunct [so1, so2])
                           (mkStEq
                              (toQualVar (mkVarDecl (mkNName 1) thing))
                              (toQualVar (mkVarDecl (mkNName 2) thing))
                           )
                        )], cSig)
            [Reflexive] ->
              do
                so <- mapObjProp cSig ope 1 1
                return ([mkForall
                           [mkVarDecl (mkNName 1) thing]
                           (mkImpl (Membership (toQualVar
                                     (mkVarDecl (mkNName 1) thing))
                                     thing nullRange)
                                   so)
                        ], cSig)
            [Irreflexive] ->
              do
                so <- mapObjProp cSig ope 1 1
                return ([mkForall
                           [mkVarDecl (mkNName 1) thing]
                           (mkImpl (Membership (toQualVar
                                     (mkVarDecl (mkNName 1) thing))
                                      thing nullRange)
                                   (mkNeg so))
                        ], cSig)
            [Symmetric] ->
              do
                 so1 <- mapObjProp cSig ope 1 2
                 so2 <- mapObjProp cSig ope 2 1
                 return ([mkForall
                           [mkVarDecl (mkNName 1) thing,
                            mkVarDecl (mkNName 2) thing]
                           (mkImpl so1 so2)
                        ], cSig)
            [Asymmetric] ->
              do
                so1 <- mapObjProp cSig ope 1 2
                so2 <- mapObjProp cSig ope 2 1
                return ([mkForall
                           [mkVarDecl (mkNName 1) thing,
                            mkVarDecl (mkNName 2) thing]
                           (mkImpl so1 (mkNeg so2))
                        ], cSig)
            [Antisymmetric] ->
              do
                so1 <- mapObjProp cSig ope 1 2
                so2 <- mapObjProp cSig ope 2 1
                return ([mkForall
                         [mkVarDecl (mkNName 1) thing,
                          mkVarDecl (mkNName 2) thing]
                         (mkImpl
                           (conjunct [so1, so2])
                           (mkStEq
                              (toQualVar (mkVarDecl (mkNName 1) thing))
                              (toQualVar (mkVarDecl (mkNName 2) thing))
                           )
                        )], cSig)
            [Transitive] ->
              do
                so1 <- mapObjProp cSig ope 1 2
                so2 <- mapObjProp cSig ope 2 3
                so3 <- mapObjProp cSig ope 1 3
                return ([mkForall
                           [mkVarDecl (mkNName 1) thing,
                             mkVarDecl (mkNName 2) thing,
                             mkVarDecl (mkNName 3) thing]
                           (mkImpl (conjunct [so1, so2]) so3)
                        ], cSig)
            _ -> fail "ObjectCharacteristics Character fail"
        _ -> fail "ObjectCharacteristics Entity fail"
-}
-- | Mapping of AnnFrameBit
mapAnnFrameBit :: Sign
               -> Extended
               -> AnnFrameBit
               -> Result ([SENTENCE], Sign)
mapAnnFrameBit cSig ex afb =
  case afb of
    AnnotationFrameBit -> return ([], cSig)
    DataFunctional ->
      case ex of
        SimpleEntity (Entity ty iri) ->
          case ty of
            DataProperty ->
                do
                  so1 <- mapDataProp cSig iri (OVar 1) (OVar 2)
                  so2 <- mapDataProp cSig iri (OVar 1) (OVar 3)
                  return ([mkQuants (mkUnivQ 
                                      [mkNAME 1, mkNAME 2, mkNAME 3]
                                     (mkBools 
                                       (mkImpl 
                                         (mkBools (cnjct [so1, so2]))
                                         (mkAtoms (mkEq (mkNTERM 2) (mkNTERM 3)))
                                       )
                                     )
                                    )
                          ], cSig)

            _ -> fail "DataFunctional EntityType fail"
        _ -> fail "DataFunctional Extend fail"
    DatatypeBit dr ->
      case ex of
        SimpleEntity (Entity ty iri) ->
          case ty of
            Datatype ->
              do
            --    odes <- mapDataRange cSig dr 2
                let dtb = uriToId iri
                return ([], cSig)
            -- TO BE IMPLEMENTED
              {-  return ([mkForall
                           [mkVarDecl (mkNName 1) thing]
                           (mkEqv
                              odes
                              (Membership
                                (toQualVar (mkVarDecl (mkNName 2) thing))
                                dtb
                                nullRange
                              )
                           )
                        ], cSig)-}
            _ -> fail "DatatypeBit EntityType fail"
        _ -> fail "DatatypeBit Extend fail"
    ClassDisjointUnion clsl ->
      case ex of
        SimpleEntity (Entity ty iri) ->
          case ty of
            Class ->
                 do
                    (decrs, dSig)  <- mapDescriptionList cSig 1 clsl
                    (decrsS, pSig) <- mapDescriptionListP cSig 1 $ comPairs clsl clsl
                    let decrsP = unzip decrsS
                    mcls <- mapClassIRI cSig iri (mkNName 1)
                    return ([mkQuants (mkUnivQ
                              [mkNAME 1]
                               (mkBools (mkBicnd
                                 mcls(
                                mkBools (cnjct
                                [(mkBools (dsjct decrs))
                                ,(mkBools (mkNeg 
                                   (mkBools (cnjct((fst decrsP) ++ (snd decrsP))))
                                ))])))))], unite dSig pSig)                               
            _ -> fail "ClassDisjointUnion EntityType fail"
        _ -> fail "ClassDisjointUnion Extend fail"
    ClassHasKey _obpe _dpe -> return ([], cSig)
    ObjectSubPropertyChain oplst ->
      do
        os <- mapM (\ cd -> mapSubObjPropChain cSig afb cd 3) oplst
        return (os, cSig)


-- | mapping of individual list
mapComIndivList :: Sign                   
                -> SameOrDifferent
                -> Maybe Individual
                -> [Individual]
                -> Result [SENTENCE]
mapComIndivList cSig sod mol inds = do
  fs <- mapM (mapIndivIRI cSig) inds
  tps <- case mol of
    Nothing -> return $ comPairs fs fs
    Just ol -> do
      f <- mapIndivIRI cSig ol
      return $ comPairsaux f fs
  let inDL = comPairs fs fs
      sntLst = (map (\ (x, y) -> case sod of
                                   Same -> mkAtoms (mkEq x y)
                                   Different -> mkBools (mkNeg (mkAtoms (mkEq x y)))) inDL)
  return $ [mkBools (cnjct sntLst)]


{- | Mapping along ObjectPropsList for creation of pairs for commutative
operations. -}
mapComObjectPropsList :: Sign                    -- ^ Signature
                      -> [ObjectPropertyExpression]
                      -> VarOrIndi                        -- ^ First variable
                      -> VarOrIndi                         -- ^ Last  variable
                      -> Result [(SENTENCE,SENTENCE)]
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
mapConstantList sig cl =
  mapM (\ x -> do
                 t <- mapConstant sig x
                 return $ t ) cl

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
                 oProps  <- mapM (\ (z, x, y) -> mapObjProp cSig z (OVar x) (OVar y)) $
                                  zip3 props ((num1 : vars) ++ [num2]) $
                                       tail ((num1 : vars) ++ [num2])
                 ooP     <- mapObjProp cSig oP (OVar num1) (OVar num2)
                 let lst = [ Name (mkNName num1)
                           , Name (mkNName num2)]
                           ++ (map (\x -> Name (mkNName x)) vars)
                 return $ Quant_sent (Universal
                           lst
                           (
                            Bool_sent (
                             Implication
                             (Bool_sent (Conjunction oProps) nullRange)
                             ooP
                            )
                            nullRange
                            )
                           )
                           nullRange
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
  return $ Quant_sent (Universal
           [ Name (mkNName num1)
           , Name (mkNName num2)]
           (
            Bool_sent
            (
            Implication
            l
            r
            )
           nullRange
           )
           )
           nullRange

{- | Mapping along DataPropsList for creation of pairs for commutative
operations. -}
mapComDataPropsList :: Sign
                      -> [DataPropertyExpression]
                      -> VarOrIndi                   -- ^ First variable
                      -> VarOrIndi                   -- ^ Last  variable
                      -> Result [(SENTENCE,SENTENCE)]
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
    return $ Atom_sent
             (
              Atom
              (
               Name_term ur
              )
              [Term_seq l, Term_seq r]
             )
             nullRange

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
              return $ Atom_sent
                        (
                        Atom
                          (
                            Name_term ur
                          )
                          [Term_seq l, Term_seq r]
                        )
                        nullRange
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
    return $ Atom_sent
             (
              Atom
              (
               Name_term ur
              )
              (
               [Term_seq (Name_term uid)]
              )
             )
             nullRange

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

uriToIdM :: IRI -> Result Id
uriToIdM = return . uriToId

-- | Mapping of a list of descriptions
mapDescriptionList :: Sign
                      -> Int
                      -> [ClassExpression]
                      -> Result ([SENTENCE], Sign)
mapDescriptionList cSig n lst = -- (zip lst $ replicate (length lst) n)
  do
    (sens, lSig) <- liftM unzip $ mapM ((\w x y z ->
                            mapDescription w z x y) cSig (OVar n) n) lst
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
      (llst, sSig)  <- mapDescriptionList cSig n l
      (rlst, tSig) <- mapDescriptionList cSig n r
      let olst = zip llst rlst
      return (olst, unite sSig tSig)

-- | Build a name
mkNName :: Int -> Token
mkNName i = mkSimpleId $ hetsPrefix ++  mkNName_H i
    where
      mkNName_H k =
          case k of
            0 -> ""
            j -> mkNName_H (j `div` 26) ++ [chr (j `mod` 26 + 96)]

-- | Get all distinct pairs for commutative operations
comPairs :: [t] -> [t1] -> [(t, t1)]
comPairs [] []     = []
comPairs _  []     = []
comPairs [] _      = []
comPairs (a:as) (_:bs) = zip (replicate (length bs) a) bs ++ comPairs as bs

comPairsaux :: t -> [t1] -> [(t, t1)]
comPairsaux a = map (\ b -> (a, b))

-- | mapping of Data Range
mapDataRange :: Sign
             -> DataRange                -- ^ OWL DataRange
             -> VarOrIndi                      -- ^ Current Variablename
             -> Result (SENTENCE, Sign)       -- ^ CommonLogic SENTENCE, Signature
mapDataRange cSig rn inId =
  do
    let uid = Name_term (voiToTok inId)
    case rn of
         DataJunction _ _ -> error "nyi"
         DataComplementOf dr ->
          do
            (dc, sig) <- mapDataRange cSig dr inId
            return (( Bool_sent (Negation dc) nullRange), sig)
         DataOneOf cs ->
          do
            cl <- mapConstantList cSig cs
            dl <- mapM (\x -> return $
                    Atom_sent (Atom x [Term_seq uid]) nullRange) cl
            return ((Bool_sent
                          (Disjunction
                            dl
                          ) nullRange), cSig)
         DataType dt rlst -> 
           do
           -- sent <- uriToTokM dt  -- NOT sure what to do with datatype here
            (sens, sigL) <- liftM unzip $ mapM (mapFacet cSig uid) rlst
            return $ ((Bool_sent (
                      Conjunction ({-sent :-} sens)
                      ) nullRange), uniteL sigL)



-- | mapping of a tuple of ConstrainingFacet and RestictionValue
mapFacet :: Sign
         -> TERM
         -> (ConstrainingFacet, RestrictionValue)
         -> Result (SENTENCE, Sign)
mapFacet sig var (f,r) =
    do
      con <- mapConstant sig r
      return $ ((Atom_sent
                (Atom
                  (Name_term (uriToTok f))
                  [ Term_seq con
                  , Term_seq var ]
                ) nullRange) , unite sig (emptySig
                   {items = Set.fromList [(stringToId (showQN f))]} ))



-- | mapping of OWL Descriptions
mapDescription :: Sign
               -> ClassExpression           -- ^ OWL ClassExpression
               -> VarOrIndi                -- ^ Current Variablename
               -> Int                      -- ^ Alternative to current
               -> Result (SENTENCE, Sign)  -- ^ CommonLogic_DL Formula
mapDescription cSig des oVar aVar =
  let varN = case oVar of
        OVar v -> mkNName v
        OIndi i -> uriToTok i
      var = case oVar of
        OVar v  -> v
        OIndi _ -> aVar
  in case des of
         Expression cl ->
           do
            rslt <- mapClassIRI cSig cl varN
            return (rslt, cSig)
         ObjectJunction jt desL ->
           do
             (desO, dSig) <- liftM unzip $ mapM ((\w x y z ->
                            mapDescription w z x y) cSig oVar aVar) desL
             return $ case jt of
                UnionOf -> ((Bool_sent (Disjunction desO) nullRange), (uniteL dSig))
                IntersectionOf -> ((Bool_sent (Conjunction desO) nullRange), (uniteL dSig))
         ObjectComplementOf descr ->
           do
             (desO, dSig) <- mapDescription cSig descr oVar  aVar
             return $ ((Bool_sent (Negation desO) nullRange), dSig)
         ObjectOneOf indS ->
           do
             indO <- mapM (mapIndivIRI cSig) indS
             let forms = map ((\x y -> Atom_sent (Equation x y)
                            nullRange) (Name_term varN)) indO
             return $ ((Bool_sent (Disjunction forms) nullRange), cSig)
         ObjectValuesFrom qt oprop descr ->
           do
             opropO <- mapObjProp cSig oprop (OVar var) (OVar (var + 1))
             (descO, dSig) <- mapDescription cSig descr (OVar (var + 1))  (aVar + 1)
             case qt of
               SomeValuesFrom ->
                    return $ ((Quant_sent (Existential [Name (mkNName
                                        (var + 1))]
                        (
                         Bool_sent (Conjunction
                         [opropO, descO])
                         nullRange
                        ))
                 nullRange), dSig)
               AllValuesFrom ->
                   return $ ((Quant_sent (Universal [Name (mkNName
                                        (var + 1))]
                        (
                         Bool_sent (Implication
                         opropO descO)
                         nullRange
                        ))
                        nullRange), dSig)
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
                            let vlst = [(var+1) .. (n+var)]
                                vLst = map (\ x -> OVar x) vlst
                                vlstM = [(var+1) .. (n+var+1)]
                                vLstM = map (\ x -> OVar x) vlstM
                            (dOut, sigL) <- (\x -> case x of
                                  Nothing -> return ([], [])
                                  Just y ->
                                    liftM unzip $ mapM (uncurry (mapDescription cSig y))
                                        (zip vLst vlst)
                                 ) d
                            let dlst = map (\(x,y) ->
                                            Bool_sent (Negation
                                            (
                                              Atom_sent (Equation
                                                (Name_term (mkNName x))
                                                (Name_term (mkNName y)))
                                                nullRange
                                            )
                                            )
                                            nullRange
                                            ) $ comPairs vlst vlst
                                dlstM = map (\(x,y) ->
                                                Atom_sent (Equation
                                                  (Name_term (mkNName x))
                                                  (Name_term (mkNName y)))
                                                  nullRange
                                            ) $ comPairs vlstM vlstM
                                qVars = map (\x ->
                                              Name (mkNName x)
                                            ) vlst
                                qVarsM = map (\x ->
                                                  Name (mkNName x)
                                             ) vlstM
                            oProps <- mapM (mapObjProp cSig oprop (OVar var)) vLst
                            oPropsM <- mapM (mapObjProp cSig oprop (OVar var)) vLstM
                            let minLst = Quant_sent (Existential
                                  qVars
                                  (
                                   Bool_sent (Conjunction
                                   (dlst ++ dOut ++ oProps))
                                   nullRange
                                  ))
                                  nullRange
                            let maxLst = Quant_sent (Universal
                                  qVarsM
                                  (
                                   Bool_sent (Implication
                                   (Bool_sent (Conjunction (oPropsM ++ dOut)) nullRange)
                                   (Bool_sent (Disjunction dlstM) nullRange))
                                   nullRange
                                  ))
                                  nullRange
                            case ct of
                               MinCardinality -> return ((minLst), cSig)
                               MaxCardinality -> return ((maxLst), cSig)
                               ExactCardinality -> return $
                                           ((Bool_sent (Conjunction
                                           [minLst, maxLst])
                                           nullRange), uniteL sigL)
         DataValuesFrom qt dpe {-dpel-} dr ->
            do
              let varNN = mkNName (var + 1)
              (drSent, drSig) <- mapDataRange cSig dr (OVar var)
              senl <- mapM (mapDataPropI cSig (OVar var) (OVar (var+1))) [dpe]
              let sent = Bool_sent ( Conjunction (drSent : senl)) nullRange
              case qt of
                   AllValuesFrom ->
                    return $ (Quant_sent (Universal [Name varNN]
                          sent ) nullRange, drSig)
                   SomeValuesFrom ->
                    return $ (Quant_sent (Existential [Name varNN]
                          sent ) nullRange, drSig)
         DataHasValue dpe c       ->
           do
             let dpet = Name_term $ uriToTok dpe
             con <- mapConstant cSig c
             return $ ((Quant_sent (Universal [Name varN] (
                  Atom_sent (
                    Atom
                      dpet
                      [ (Term_seq (Name_term (varN)))
                      , (Term_seq con)]
                  ) nullRange)
                  ) nullRange), cSig)
         DataCardinality c ->
             case c of
                  Cardinality ct n dpe dr
                    ->
                      do
                        let vlst  = [(var+1) .. (n+var)]
                            vLst = map (\ x -> OVar x) vlst
                            vlstM = [(var+1) .. (n+var+1)]
                            vLstM = map (\ x -> OVar x) vlstM
                        (dOut, sigL) <- (\x -> case x of
                              Nothing -> return ([], [])
                              Just y ->
                                liftM unzip $ mapM (mapDataRange cSig y) vLst
                             ) dr
                        let dlst = map (\(x,y) ->
                                        Bool_sent (Negation
                                        (
                                          Atom_sent (Equation
                                            (Name_term (mkNName x))
                                            (Name_term (mkNName y)))
                                            nullRange
                                        )
                                        )
                                        nullRange
                                        ) $ comPairs vlst vlst
                            dlstM = map (\(x,y) ->
                                            Atom_sent (Equation
                                              (Name_term (mkNName x))
                                              (Name_term (mkNName y)))
                                              nullRange
                                        ) $ comPairs vlstM vlstM
                            qVars = map (\x ->
                                          Name (mkNName x)
                                        ) vlst
                            qVarsM = map (\x ->
                                              Name (mkNName x)
                                          ) vlstM
                        dProps <- mapM (mapDataProp cSig dpe (OVar var)) vLst
                        dPropsM <- mapM (mapDataProp cSig dpe (OVar var)) vLstM
                        let minLst = Quant_sent (Existential
                              qVars
                              (
                                Bool_sent (Conjunction
                                (dlst ++ dOut ++ dProps))
                                nullRange
                              ))
                              nullRange
                        let maxLst = Quant_sent (Universal
                              qVarsM
                              (
                                Bool_sent (Implication
                                (Bool_sent (Conjunction (dPropsM ++ dOut)) nullRange)
                                (Bool_sent (Disjunction dlstM) nullRange))
                                nullRange
                              ))
                              nullRange
                        case ct of
                            MinCardinality -> return ((minLst), cSig)
                            MaxCardinality -> return ((maxLst), cSig)
                            ExactCardinality -> return $
                                        ((Bool_sent (Conjunction
                                        [minLst, maxLst])
                                        nullRange), uniteL sigL)
