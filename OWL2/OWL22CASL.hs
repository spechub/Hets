{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  Comorphism from OWL 2 to CASL_Dl
Copyright   :  (c) Francisc-Nicolae Bungiu
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
import OWL2.Parse
import OWL2.ProfilesAndSublogics
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
import Common.DocUtils

import Data.Maybe
import Text.ParserCombinators.Parsec

data OWL22CASL = OWL22CASL deriving Show

instance Language OWL22CASL

instance Comorphism
    OWL22CASL        -- comorphism
    OWL2             -- lid domain
    ProfSub          -- sublogics domain
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
      sourceSublogic OWL22CASL = topS
      targetLogic OWL22CASL = CASL
      mapSublogic OWL22CASL _ = Just $ cFol
        { cons_features = emptyMapConsFeature }
      map_theory OWL22CASL = mapTheory
      map_morphism OWL22CASL = mapMorphism
      map_symbol OWL22CASL _ = mapSymbol
      isInclusionComorphism OWL22CASL = True
      has_model_expansion OWL22CASL = True

failMsg :: Pretty a => a -> Result b
failMsg a = fail $ "cannot translate " ++ showDoc a "\n"

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

mapSymbol :: Entity -> Set.Set Symbol
mapSymbol (Entity ty iri) = let
  syN = Set.singleton . Symbol (uriToId iri)
  in case ty of
  Class -> syN $ PredAsItemType conceptPred
  ObjectProperty -> syN $ PredAsItemType objectPropPred
  DataProperty -> syN $ PredAsItemType dataPropPred
  NamedIndividual -> syN $ OpAsItemType indiConst
  AnnotationProperty -> Set.empty
  Datatype -> Set.empty

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

loadDataInformation :: ProfSub -> Sign f ()
loadDataInformation _ = let dts = Set.fromList $ map stringToId datatypeKeys
    in (emptySign ()) { sortRel = Rel.fromKeysSet dts }

mapTheory :: (OS.Sign, [Named Axiom])
             -> Result (CASLSign, [Named CASLFORMULA])
mapTheory (owlSig, owlSens) = let sl = topS in do
    cSig <- mapSign owlSig
    let pSig = loadDataInformation sl
    (cSens, nSig) <- foldM (\ (x, y) z -> do
            (sen, sig) <- mapSentence y z
            return (sen ++ x, uniteCASLSign sig y)) ([], cSig) owlSens
    return (uniteCASLSign nSig pSig, predefinedAxioms ++ cSens)

-- | mapping of OWL to CASL_DL formulae
mapSentence :: CASLSign                           -- ^ CASL Signature
  -> Named Axiom                                  -- ^ OWL2 Sentence
  -> Result ([Named CASLFORMULA], CASLSign) -- ^ CASL Sentence
mapSentence cSig inSen = do
    (outAx, outSig) <- mapAxioms cSig $ sentence inSen
    return (map (flip mapNamed inSen . const) outAx, outSig)

mapAxioms :: CASLSign -> Axiom -> Result ([CASLFORMULA], CASLSign)
mapAxioms cSig (PlainAxiom ex fb) = case fb of
    ListFrameBit rel lfb -> mapListFrameBit cSig ex rel lfb
    AnnFrameBit _ afb -> mapAnnFrameBit cSig ex afb

toIRILst :: EntityType -> Extended -> Maybe IRI
toIRILst ty ane = case ane of
  SimpleEntity (Entity ty2 iri) | ty == ty2 -> Just iri
  _ -> Nothing

tokDecl :: Token -> VAR_DECL
tokDecl = flip mkVarDecl thing

nameDecl :: Int -> SORT -> VAR_DECL
nameDecl = mkVarDecl . mkNName

thingDecl :: Int -> VAR_DECL
thingDecl = flip nameDecl thing

dataDecl :: Int -> VAR_DECL
dataDecl = flip nameDecl dataS

qualThing :: Int -> TERM f
qualThing = toQualVar . thingDecl

implConj :: [FORMULA f] -> FORMULA f -> FORMULA f
implConj = mkImpl . conjunct

mkEqVar :: VAR_DECL -> TERM f -> FORMULA f
mkEqVar = mkStEq . toQualVar

mkFEI :: [VAR_DECL] -> [VAR_DECL] -> FORMULA f -> FORMULA f -> FORMULA f
mkFEI l1 l2 f = mkForall l1 . mkExist l2 . mkImpl f

mapFact :: CASLSign -> Extended -> Fact -> Result CASLFORMULA
mapFact cSig ex f = case f of
    ObjectPropertyFact posneg obe ind -> case ex of
        SimpleEntity (Entity NamedIndividual siri) -> do
            inS <- mapIndivURI cSig siri
            inT <- mapIndivURI cSig ind
            oPropH <- mapObjProp cSig obe 1 2
            let oProp = case posneg of
                    Positive -> oPropH
                    Negative -> Negation oPropH nullRange
            return $ mkForall (map thingDecl [1, 2]) $ implConj
                            [mkEqVar (thingDecl 1) inS,
                             mkEqVar (thingDecl 2) inT] oProp
        _ -> fail $ "ObjectPropertyFactsFacts Entity fail: " ++ show ex
    DataPropertyFact posneg dpe lit -> case ex of
        SimpleEntity (Entity NamedIndividual iri) -> do
            inS <- mapIndivURI cSig iri
            inT <- mapLiteral lit
            oPropH <- mapDataProp cSig dpe 1 2
            let oProp = case posneg of
                    Positive -> oPropH
                    Negative -> Negation oPropH nullRange
            return $ mkForall [thingDecl 1, dataDecl 2] $ implConj
                [mkEqVar (thingDecl 1) inS,
                 mkEqVar (dataDecl 2) $ upcast inT dataS] oProp

        _ -> fail "DataPropertyFact Entity fail"

-- | Mapping of ListFrameBit
mapListFrameBit :: CASLSign -> Extended -> Maybe Relation -> ListFrameBit
       -> Result ([CASLFORMULA], CASLSign)
mapListFrameBit cSig ex rel lfb = case lfb of
    AnnotationBit _ -> return ([], cSig)
    ExpressionBit cls -> case ex of
          Misc _ -> return ([], cSig)
          SimpleEntity (Entity ty iri) -> case ty of
              NamedIndividual | rel == Just Types -> do
                  inD <- mapIndivURI cSig iri
                  ocls <- mapM (\ (_, c) -> mapDescription cSig c 1) cls
                  return (map (mkForall [thingDecl 1] . mkImpl (mkEqVar
                          (thingDecl 1) inD)) ocls, cSig)
              DataProperty | rel == (Just $ DRRelation ADomain) -> do
                  oEx <- mapDataProp cSig iri 1 2
                  odes <- mapM (\ (_, c) -> mapDescription cSig c 1) cls
                  let vars = (mkNName 1, mkNName 2)
                  return (map (mkFEI [tokDecl (fst vars)]
                        [mkVarDecl (snd vars) dataS] oEx) odes, cSig)
              _ -> failMsg lfb
          ObjectEntity oe -> case rel of
              Nothing -> return ([], cSig)
              Just re -> case re of
                  DRRelation r -> do
                    tobjP <- mapObjProp cSig oe 1 2
                    tdsc <- mapM (\ (_, c) -> mapDescription cSig c $ case r of
                        ADomain -> 1
                        ARange -> 2) cls
                    let vars = case r of
                                 ADomain -> (mkNName 1, mkNName 2)
                                 ARange -> (mkNName 2, mkNName 1)
                    return (map (mkFEI [tokDecl $ fst vars]
                            [tokDecl $ snd vars] tobjP) tdsc, cSig)
                  _ -> failMsg lfb
          ClassEntity ce -> do
            let map2nd = map snd cls
            case rel of
              Nothing -> return ([], cSig)
              Just r -> case r of
                EDRelation re -> do
                    decrsS <- mapDescriptionListP cSig 1
                      $ comPairsaux ce map2nd
                    let decrsP = map (\ (x, y) -> mkForall [thingDecl 1]
                            $ case re of
                                Equivalent -> mkEqv x y
                                Disjoint -> mkNeg $ conjunct [x, y]) decrsS
                    return (decrsP, cSig)
                SubClass -> do
                  domT <- mapDescription cSig ce 1
                  codT <- mapDescriptionList cSig 1 map2nd
                  return (map (mkForall [thingDecl 1] . mkImpl domT) codT, cSig)
                _ -> failMsg lfb
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
          return (map (\ (a, b) -> mkForall (map thingDecl [1, 2]) $ case ed of
                            Equivalent -> mkEqv a b
                            Disjoint -> mkNeg $ conjunct [a, b]) pairs, cSig)
        SubPropertyOf | isJ -> do
                  os <- mapM (\ (o1, o2) -> mapSubObjProp cSig o1 o2 3)
                    $ comPairsaux ob map2nd
                  return (os, cSig)
        InverseOf | isJ -> do
             os1 <- mapM (\ o1 -> mapObjProp cSig o1 1 2) map2nd
             o2 <- mapObjProp cSig ob 2 1
             return (map (mkForall (map thingDecl [1, 2]) . mkEqv o2) os1, cSig)
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
          return (map (mkForall [thingDecl 1, dataDecl 2]
                    . mkImpl o2) os1, cSig)
        EDRelation ed -> do
          pairs <- mapComDataPropsList cSig map2nd 1 2
          return (map (\ (a, b) -> mkForall (map thingDecl [1, 2]) $ case ed of
                        Equivalent -> mkEqv a b
                        Disjoint -> mkNeg $ conjunct [a, b]) pairs, cSig)
        _ -> return ([], cSig)
    IndividualSameOrDifferent al -> do
        let mol = toIRILst NamedIndividual ex
            map2nd = map snd al
        case rel of
          Nothing -> return ([], cSig)
          Just r -> case r of
              SDRelation re -> do
                fs <- mapComIndivList cSig re mol map2nd
                return (fs, cSig)
              _ -> return ([], cSig)
    DataPropRange dpr -> case ex of
        SimpleEntity (Entity DataProperty iri) -> do
            oEx <- mapDataProp cSig iri 1 2
            odes <- mapM (\ (_, c) -> mapDataRange cSig c 2) dpr
            let vars = (mkNName 1, mkNName 2)
            return (map (mkFEI [tokDecl $ fst vars] [tokDecl $ snd vars] oEx)
                        odes, cSig)
        _ -> failMsg lfb
    IndividualFacts indf -> do
        fl <- mapM (mapFact cSig ex . snd) indf
        return (fl, cSig)
    ObjectCharacteristics ace -> case ex of
        ObjectEntity ope -> do
            cl <- mapM (mapCharact cSig ope . snd) ace
            return (cl, cSig)
        _ -> failMsg ace

mkFI :: [Int] -> [FORMULA f] -> Int -> Int -> FORMULA f
mkFI l1 l2 x y = mkForall (map thingDecl l1) $ implConj l2 $ mkEqVar
        (thingDecl x) $ qualThing y

mkRI :: [Int] -> Int -> FORMULA f -> FORMULA f
mkRI l x so = mkForall (map thingDecl l) $ mkImpl
            (Membership (qualThing x) thing nullRange) so

mapCharact :: CASLSign -> ObjectPropertyExpression -> Character
            -> Result CASLFORMULA
mapCharact cSig ope c = case c of
    Functional -> do
        so1 <- mapObjProp cSig ope 1 2
        so2 <- mapObjProp cSig ope 1 3
        return $ mkFI [1, 2, 3] [so1, so2] 2 3
    InverseFunctional -> do
        so1 <- mapObjProp cSig ope 1 3
        so2 <- mapObjProp cSig ope 2 3
        return $ mkFI [1, 2, 3] [so1, so2] 1 2
    Reflexive -> do
        so <- mapObjProp cSig ope 1 1
        return $ mkRI [1] 1 so
    Irreflexive -> do
        so <- mapObjProp cSig ope 1 1
        return $ mkRI [1] 1 $ mkNeg so
    Symmetric -> do
        so1 <- mapObjProp cSig ope 1 2
        so2 <- mapObjProp cSig ope 2 1
        return $ mkForall (map thingDecl [1, 2]) $ mkImpl so1 so2
    Asymmetric -> do
        so1 <- mapObjProp cSig ope 1 2
        so2 <- mapObjProp cSig ope 2 1
        return $ mkForall (map thingDecl [1, 2]) $ mkImpl so1 $ mkNeg so2
    Antisymmetric -> do
        so1 <- mapObjProp cSig ope 1 2
        so2 <- mapObjProp cSig ope 2 1
        return $ mkFI [1, 2] [so1, so2] 1 2
    Transitive -> do
        so1 <- mapObjProp cSig ope 1 2
        so2 <- mapObjProp cSig ope 2 3
        so3 <- mapObjProp cSig ope 1 3
        return $ mkForall (map thingDecl [1, 2, 3]) $ implConj [so1, so2] so3

-- | Mapping of AnnFrameBit
mapAnnFrameBit :: CASLSign -> Extended -> AnnFrameBit
            -> Result ([CASLFORMULA], CASLSign)
mapAnnFrameBit cSig ex afb =
    let err = fail $ "could not translate " ++ show afb in case afb of
    AnnotationFrameBit _ -> return ([], cSig)
    DataFunctional -> case ex of
        SimpleEntity (Entity _ iri) -> do
            so1 <- mapDataProp cSig iri 1 2
            so2 <- mapDataProp cSig iri 1 3
            return ([mkForall (thingDecl 1 : map dataDecl [2, 3]) $ implConj
                        [so1, so2] $ mkEqVar (thingDecl 2) $ qualThing 3], cSig)
        _ -> err
    DatatypeBit dr -> case ex of
        SimpleEntity (Entity Datatype iri) -> do
            odes <- mapDataRange cSig dr 2
            let dtb = uriToId iri
            return ([mkForall [thingDecl 1] $ mkEqv odes $ Membership
                    (qualThing 2) dtb nullRange], cSig)
        _ -> err
    ClassDisjointUnion clsl -> case ex of
        SimpleEntity (Entity Class iri) -> do
            decrs <- mapDescriptionList cSig 1 clsl
            decrsS <- mapDescriptionListP cSig 1 $ comPairs clsl clsl
            let decrsP = map (\ (x, y) -> conjunct [x, y]) decrsS
            mcls <- mapClassURI cSig iri $ mkNName 1
            return ([mkForall [thingDecl 1] $ mkEqv mcls $ conjunct
                    [disjunct decrs, mkNeg $ conjunct decrsP]], cSig)
        _ -> err
    ClassHasKey _ _ -> return ([], cSig)
    ObjectSubPropertyChain oplst -> do
        os <- mapM (\ cd -> mapSubObjPropChain cSig oplst cd 3) oplst
        return (os, cSig)

-- | Mapping of ObjectSubPropertyChain
mapSubObjPropChain :: CASLSign -> [ObjectPropertyExpression]
    -> ObjectPropertyExpression -> Int -> Result CASLFORMULA
mapSubObjPropChain cSig props oP num1 = let num2 = num1 + 1 in do
    let zprops = zip (tail props) [(num2 + 1) ..]
        (_, vars) = unzip zprops
    oProps <- mapM (\ (z, x, y) -> mapObjProp cSig z x y) $
                zip3 props (num1 : vars ++ [num2]) $
                tail $ num1 : vars ++ [num2]
    ooP <- mapObjProp cSig oP num1 num2
    return $ mkForall (map thingDecl [1, 2]) $ mkForall
                (map thingDecl vars) $ mkImpl (conjunct oProps) ooP

{- | Mapping along ObjectPropsList for creation of pairs for commutative
operations. -}
mapComObjectPropsList :: CASLSign -> Maybe ObjectPropertyExpression
    -> [ObjectPropertyExpression] -> Int -> Int
    -> Result [(CASLFORMULA, CASLFORMULA)]
mapComObjectPropsList cSig mol props num1 num2 = do
    fs <- mapM (\ x -> mapObjProp cSig x num1 num2) props
    case mol of
        Nothing -> return $ comPairs fs fs
        Just ol -> do
            f <- mapObjProp cSig ol num1 num2
            return $ comPairsaux f fs

-- | mapping of individual list
mapComIndivList :: CASLSign -> SameOrDifferent -> Maybe Individual
    -> [Individual] -> Result [CASLFORMULA]
mapComIndivList cSig sod mol inds = do
    fs <- mapM (mapIndivURI cSig) inds
    tps <- case mol of
        Nothing -> return $ comPairs fs fs
        Just ol -> do
            f <- mapIndivURI cSig ol
            return $ comPairsaux f fs
    return $ map (\ (x, y) -> case sod of
        Same -> mkStEq x y
        Different -> mkNeg $ mkStEq x y) tps

-- | Mapping of subobj properties
mapSubObjProp :: CASLSign -> ObjectPropertyExpression
    -> ObjectPropertyExpression -> Int -> Result CASLFORMULA
mapSubObjProp cSig oPL oP num1 = do
    let num2 = num1 + 1
    l <- mapObjProp cSig oPL num1 num2
    r <- mapObjProp cSig oP num1 num2
    return $ mkForallRange (map thingDecl [num1, num2]) (mkImpl r l ) nullRange

{- | Mapping along DataPropsList for creation of pairs for commutative
operations. -}
mapComDataPropsList :: CASLSign -> [DataPropertyExpression] -> Int -> Int
        -> Result [(CASLFORMULA, CASLFORMULA)]
mapComDataPropsList cSig props num1 num2 = mapM (\ (x, z) -> do
    l <- mapDataProp cSig x num1 num2
    r <- mapDataProp cSig z num1 num2
    return (l, r)) $ comPairs props props

mapNNInt :: NNInt -> TERM ()
mapNNInt int = let NNInt uInt = int in foldr1 joinDigits $ map mkDigit uInt

mapIntLit :: IntLit -> TERM ()
mapIntLit int =
    let cInt = mapNNInt $ absInt int
    in if isNegInt int then negateInt $ upcast cInt integer
        else upcast cInt integer

mapDecLit :: DecLit -> TERM ()
mapDecLit dec =
    let ip = truncDec dec
        np = absInt ip
        fp = fracDec dec
        n = mkDecimal (mapNNInt np) (mapNNInt fp)
    in if isNegInt ip then negateFloat n else n

mapFloatLit :: FloatLit -> TERM ()
mapFloatLit f =
    let fb = floatBase f
        ex = floatExp f
     in mkFloat (mapDecLit fb) (mapIntLit ex)

mapNrLit :: Literal -> TERM ()
mapNrLit l = case l of
    NumberLit f
        | isFloatInt f -> mapIntLit $ truncDec $ floatBase f
        | isFloatDec f -> mapDecLit $ floatBase f
        | otherwise -> mapFloatLit f
    _ -> error "not number literal"

mapLiteral :: Literal -> Result (TERM ())
mapLiteral lit = return $ case lit of
    Literal l ty -> Sorted_term (case ty of
        Untyped _ -> foldr consChar emptyStringTerm l
        Typed dt -> case datatypeType dt of
            OWL2Number -> let p = parse literal "" l in case p of
                Right nr -> mapNrLit nr
                _ -> error "cannot parse number literal"
            OWL2Bool -> case l of
                "true" -> trueT
                _ -> falseT
            _ -> foldr consChar emptyStringTerm l) dataS nullRange
    _ -> mapNrLit lit

mkThingVar :: VAR -> TERM f
mkThingVar v = Qual_var v thing nullRange

-- | Mapping of data properties
mapDataProp :: CASLSign -> DataPropertyExpression -> Int -> Int
            -> Result CASLFORMULA
mapDataProp _ dP nO nD = do
      let l = mkNName nO
          r = mkNName nD
      ur <- uriToIdM dP
      return $ mkPred ur dataPropPred [Qual_var l thing nullRange,
                Qual_var r dataS nullRange]

-- | Mapping of obj props
mapObjProp :: CASLSign -> ObjectPropertyExpression -> Int -> Int
        -> Result CASLFORMULA
mapObjProp cSig ob num1 num2 = case ob of
      ObjectProp u -> do
            let l = mkNName num1
                r = mkNName num2
            ur <- uriToIdM u
            return $ mkPred ur objectPropPred (map mkThingVar [l, r])
      ObjectInverseOf u -> mapObjProp cSig u num2 num1

-- | Mapping of obj props with Individuals
mapObjPropI :: CASLSign -> ObjectPropertyExpression -> VarOrIndi -> VarOrIndi
              -> Result CASLFORMULA
mapObjPropI cSig ob lP rP = case ob of
    ObjectProp u -> do
        lT <- case lP of
            OVar num1 -> return $ mkThingVar (mkNName num1)
            OIndi indivID -> mapIndivURI cSig indivID
        rT <- case rP of
            OVar num1 -> return $ mkThingVar (mkNName num1)
            OIndi indivID -> mapIndivURI cSig indivID
        ur <- uriToIdM u
        return $ mkPred ur objectPropPred [lT, rT]
    ObjectInverseOf u -> mapObjPropI cSig u rP lP

mkPred :: PRED_NAME -> PredType -> [TERM f] -> FORMULA f
mkPred u c = mkPredication $ mkQualPred u $ toPRED_TYPE c

-- | Mapping of Class URIs
mapClassURI :: CASLSign -> Class -> Token -> Result CASLFORMULA
mapClassURI _ uril uid = do
    ur <- uriToIdM uril
    return $ mkPred ur conceptPred [mkThingVar uid]

-- | Mapping of Individual URIs
mapIndivURI :: CASLSign -> Individual -> Result (TERM ())
mapIndivURI _ uriI = do
    ur <- uriToIdM uriI
    return $ mkAppl (mkQualOp ur (Op_type Total [] thing nullRange)) []

uriToIdM :: IRI -> Result Id
uriToIdM = return . uriToId

-- | Extracts Id from URI
uriToId :: IRI -> Id
uriToId urI =
    let l = localPart urI
        ur = if isThing urI then mkQName l else urI
        repl a = if isAlphaNum a then [a] else "_u"
        nP = concatMap repl $ namePrefix ur
        lP = concatMap repl l
    in stringToId $ nP ++ "" ++ lP

-- | Mapping of a list of descriptions
mapDescriptionList :: CASLSign -> Int -> [ClassExpression]
        -> Result [CASLFORMULA]
mapDescriptionList cSig n lst = mapM (uncurry $ mapDescription cSig)
        $ zip lst $ replicate (length lst) n

-- | Mapping of a list of pairs of descriptions
mapDescriptionListP :: CASLSign -> Int -> [(ClassExpression, ClassExpression)]
                    -> Result [(CASLFORMULA, CASLFORMULA)]
mapDescriptionListP cSig n lst = do
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
mapDataRange :: CASLSign -> DataRange -> Int -> Result CASLFORMULA
mapDataRange cSig dr inId = do
    let uid = mkNName inId
    case dr of
        DataType d _ -> do
            ur <- uriToIdM d
            return $ Membership (Qual_var uid thing nullRange) ur nullRange
        DataComplementOf drc -> fmap mkNeg $ mapDataRange cSig drc inId
        _ -> fail $ "could not translate " ++ show dr

-- | mapping of OWL2 Descriptions
mapDescription :: CASLSign -> ClassExpression -> Int -> Result CASLFORMULA
mapDescription cSig desc var = case desc of
    Expression u -> mapClassURI cSig u $ mkNName var
    ObjectJunction ty ds -> do
        des0 <- mapM (flip (mapDescription cSig) var) ds
        return $ case ty of
            UnionOf -> disjunct des0
            IntersectionOf -> conjunct des0
    ObjectComplementOf d -> fmap mkNeg $ mapDescription cSig d var
    ObjectOneOf is -> do
        ind0 <- mapM (mapIndivURI cSig) is
        return $ disjunct $ map (mkStEq $ qualThing var) ind0
    ObjectValuesFrom ty o d -> do
        oprop0 <- mapObjProp cSig o var (var + 1)
        desc0 <- mapDescription cSig d (var + 1)
        case ty of
            SomeValuesFrom -> return $ mkExist [thingDecl $ var + 1]
                                (conjunct [oprop0, desc0])
            AllValuesFrom -> return $ mkForall [thingDecl $ var + 1]
                                (mkImpl oprop0 desc0)
    ObjectHasSelf o -> mapObjProp cSig o var var
    ObjectHasValue o i -> mapObjPropI cSig o (OVar var) (OIndi i)
    ObjectCardinality (Cardinality ct n oprop d) -> do
        let vlst = map (var +) [1 .. n]
            vlstM = vlst ++ [n + var + 1]
        dOut <- case d of
                    Nothing -> return []
                    Just ex -> mapM (mapDescription cSig ex) vlst
        let dlst = map (\ (x, y) -> mkNeg $ mkStEq (qualThing x) $ qualThing y)
                        $ comPairs vlst vlst
            dlstM = map (\ (x, y) -> mkStEq (qualThing x) $ qualThing y)
                        $ comPairs vlstM vlstM
            qVars = map thingDecl vlst
            qVarsM = map thingDecl vlstM
        oProps <- mapM (mapObjProp cSig oprop var) vlst
        oPropsM <- mapM (mapObjProp cSig oprop var) vlstM
        let minLst = mkExist qVars $ conjunct $ dlst ++ dOut ++ oProps
        let maxLst = mkForall qVarsM $ mkImpl (conjunct $ oPropsM ++ dOut)
                        $ disjunct dlstM
        return $ case ct of
            MinCardinality -> minLst
            MaxCardinality -> maxLst
            ExactCardinality -> conjunct [minLst, maxLst]
    DataValuesFrom ty dpe dr -> do
        oprop0 <- mapDataProp cSig dpe var (var + 1)
        desc0 <- mapDataRange cSig dr (var + 1)
        return $ case ty of
            SomeValuesFrom -> mkExist [thingDecl $ var + 1]
                    $ conjunct [oprop0, desc0]
            AllValuesFrom -> mkForall [thingDecl $ var + 1]
                    $ mkImpl oprop0 desc0
    _ -> fail $ "could not translate " ++ show desc
