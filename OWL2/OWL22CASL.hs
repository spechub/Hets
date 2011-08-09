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

objectPropPred :: PredType
objectPropPred = PredType [thing, thing]

dataPropPred :: PredType
dataPropPred = PredType [thing, dataS]

indiConst :: OpType
indiConst = OpType Total [] thing

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

qualData :: Int -> TERM f
qualData = toQualVar . dataDecl

implConj :: [FORMULA f] -> FORMULA f -> FORMULA f
implConj = mkImpl . conjunct

mkEqVar :: VAR_DECL -> TERM f -> FORMULA f
mkEqVar = mkStEq . toQualVar

mkFEI :: [VAR_DECL] -> [VAR_DECL] -> FORMULA f -> FORMULA f -> FORMULA f
mkFEI l1 l2 f = mkForall l1 . mkExist l2 . mkImpl f

mkFIE :: [Int] -> [FORMULA f] -> Int -> Int -> FORMULA f
mkFIE l1 l2 x y = mkForall (map thingDecl l1) $ implConj l2 $ mkEqVar
        (thingDecl x) $ qualThing y

mkRI :: [Int] -> Int -> FORMULA f -> FORMULA f
mkRI l x so = mkForall (map thingDecl l) $ mkImpl
            (mkMember (qualThing x) thing) so

mkThingVar :: VAR -> TERM f
mkThingVar v = Qual_var v thing nullRange

mkDataVar :: VAR -> TERM f
mkDataVar v = Qual_var v dataS nullRange

mkPred :: PredType -> [TERM f] -> PRED_NAME -> FORMULA f
mkPred c tl u = mkPredication (mkQualPred u $ toPRED_TYPE c) tl

mkMember :: TERM f -> SORT -> FORMULA f
mkMember t s = Membership t s nullRange

-- | Get all distinct pairs for commutative operations
comPairs :: [t] -> [t1] -> [(t, t1)]
comPairs [] [] = []
comPairs _ [] = []
comPairs [] _ = []
comPairs (a : as) (_ : bs) = mkPairs a bs ++ comPairs as bs

mkPairs :: t -> [s] -> [(t, s)]
mkPairs a = map (\ b -> (a, b))

data VarOrIndi = OVar Int | OIndi IRI
    deriving (Show, Eq, Ord)

-- | Mapping of OWL morphisms to CASL morphisms
mapMorphism :: OWLMorphism -> Result CASLMor
mapMorphism oMor = do
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
            sen <- mapSentence z
            return (sen ++ x, y)) ([], cSig) owlSens
    return (uniteCASLSign nSig pSig, predefinedAxioms ++ cSens)

-- | mapping of OWL to CASL_DL formulae
mapSentence :: Named Axiom -> Result [Named CASLFORMULA]
mapSentence inSen = fmap (map $ flip mapNamed inSen . const)
    $ mapAxioms $ sentence inSen

toIRILst :: EntityType -> Extended -> Maybe IRI
toIRILst ty ane = case ane of
  SimpleEntity (Entity ty2 iri) | ty == ty2 -> Just iri
  _ -> Nothing

-- | Mapping of Class URIs
mapClassURI :: Class -> Token -> Result CASLFORMULA
mapClassURI c t = fmap (mkPred conceptPred [mkThingVar t]) $ uriToIdM c

-- | Mapping of Individual URIs
mapIndivURI :: Individual -> Result (TERM ())
mapIndivURI uriI = do
    ur <- uriToIdM uriI
    return $ mkAppl (mkQualOp ur (Op_type Total [] thing nullRange)) []

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

-- | mapping of individual list
mapComIndivList :: SameOrDifferent -> Maybe Individual -> [Individual]
    -> Result [CASLFORMULA]
mapComIndivList sod mol inds = do
    fs <- mapM mapIndivURI inds
    tps <- case mol of
        Nothing -> return $ comPairs fs fs
        Just ol -> fmap (`mkPairs` fs) $ mapIndivURI ol
    return $ map (\ (x, y) -> case sod of
        Same -> mkStEq x y
        Different -> mkNeg $ mkStEq x y) tps

{- | Mapping along DataPropsList for creation of pairs for commutative
operations. -}
mapComDataPropsList :: [DataPropertyExpression] -> Int -> Int
    -> Result [(CASLFORMULA, CASLFORMULA)]
mapComDataPropsList props num1 num2 = mapM (\ (x, z) -> do
    l <- mapDataProp x num1 num2
    r <- mapDataProp z num1 num2
    return (l, r)) $ comPairs props props

-- | Mapping of data properties
mapDataProp :: DataPropertyExpression -> Int -> Int -> Result CASLFORMULA
mapDataProp dp a b = fmap (mkPred dataPropPred [qualThing a, qualData b])
    $ uriToIdM dp

-- | Mapping of obj props
mapObjProp :: ObjectPropertyExpression -> Int -> Int
    -> Result CASLFORMULA
mapObjProp ob a b = case ob of
      ObjectProp u -> fmap (mkPred objectPropPred $ map qualThing [a, b])
            $ uriToIdM u
      ObjectInverseOf u -> mapObjProp u b a

-- | Mapping of obj props with Individuals
mapObjPropI :: ObjectPropertyExpression -> VarOrIndi -> VarOrIndi
    -> Result CASLFORMULA
mapObjPropI ob lP rP = case ob of
    ObjectProp u -> do
        l <- case lP of
            OVar n -> return $ qualThing n
            OIndi i -> mapIndivURI i
        r <- case rP of
            OVar n -> return $ qualThing n
            OIndi i -> mapIndivURI i
        fmap (mkPred objectPropPred [l, r]) $ uriToIdM u
    ObjectInverseOf u -> mapObjPropI u rP lP

-- | Mapping of ObjectSubPropertyChain
mapSubObjPropChain :: [ObjectPropertyExpression]
    -> ObjectPropertyExpression -> Int -> Result CASLFORMULA
mapSubObjPropChain props oP n = let m = n + 1 in do
    let zprops = zip (tail props) [(m + 1) ..]
        (_, vars) = unzip zprops
        vl = n : vars ++ [m]
    oProps <- mapM (\ (z, x, y) -> mapObjProp z x y) $
                zip3 props vl $ tail vl
    ooP <- mapObjProp oP n m
    return $ mkForall (map thingDecl [1, 2]) $ mkForall
                (map thingDecl vars) $ implConj oProps ooP

{- | Mapping along ObjectPropsList for creation of pairs for commutative
operations. -}
mapComObjectPropsList :: Maybe ObjectPropertyExpression
    -> [ObjectPropertyExpression] -> Int -> Int
    -> Result [(CASLFORMULA, CASLFORMULA)]
mapComObjectPropsList mol props a b = do
    fs <- mapM (\ x -> mapObjProp x a b) props
    case mol of
        Nothing -> return $ comPairs fs fs
        Just ol -> fmap (`mkPairs` fs) $ mapObjProp ol a b

-- | Mapping of subobj properties
mapSubObjProp :: ObjectPropertyExpression
    -> ObjectPropertyExpression -> Int -> Result CASLFORMULA
mapSubObjProp e1 e2 a = do
    let b = a + 1
    l <- mapObjProp e1 a b
    r <- mapObjProp e2 a b
    return $ mkForallRange (map thingDecl [a, b]) (mkImpl r l ) nullRange

-- | mapping of Data Range
mapDataRange :: DataRange -> Int -> Result CASLFORMULA
mapDataRange dr i = case dr of
    DataType d _ -> fmap (mkMember $ qualThing i) $ uriToIdM d
    DataComplementOf drc -> fmap mkNeg $ mapDataRange drc i
    _ -> fail $ "could not translate " ++ show dr

-- | Mapping of a list of descriptions
mapDescriptionList :: Int -> [ClassExpression]
        -> Result [CASLFORMULA]
mapDescriptionList n lst = mapM (uncurry mapDescription)
        $ zip lst $ replicate (length lst) n

-- | Mapping of a list of pairs of descriptions
mapDescriptionListP :: Int -> [(ClassExpression, ClassExpression)]
                    -> Result [(CASLFORMULA, CASLFORMULA)]
mapDescriptionListP n lst = do
    let (l, r) = unzip lst
    lls <- mapDescriptionList n l
    rls <- mapDescriptionList n r
    return $ zip lls rls

-- | mapping of OWL2 Descriptions
mapDescription :: ClassExpression -> Int -> Result CASLFORMULA
mapDescription desc var = case desc of
    Expression u -> mapClassURI u $ mkNName var
    ObjectJunction ty ds -> fmap (case ty of
                UnionOf -> disjunct
                IntersectionOf -> conjunct)
            $ mapM (flip mapDescription var) ds
    ObjectComplementOf d -> fmap mkNeg $ mapDescription d var
    ObjectOneOf is -> fmap (disjunct . map (mkStEq $ qualThing var))
            $ mapM mapIndivURI is
    ObjectValuesFrom ty o d -> let n = var + 1 in do
        oprop0 <- mapObjProp o var n
        desc0 <- mapDescription d n
        return $ case ty of
            SomeValuesFrom -> mkExist [thingDecl n] $ conjunct [oprop0, desc0]
            AllValuesFrom -> mkForall [thingDecl n] $ mkImpl oprop0 desc0
    ObjectHasSelf o -> mapObjProp o var var
    ObjectHasValue o i -> mapObjPropI o (OVar var) (OIndi i)
    ObjectCardinality (Cardinality ct n oprop d) -> do
        let vlst = map (var +) [1 .. n]
            vlstM = vlst ++ [n + var + 1]
        dOut <- case d of
                    Nothing -> return []
                    Just ex -> mapM (mapDescription ex) vlst
        let dlst = map (\ (x, y) -> mkNeg $ mkStEq (qualThing x) $ qualThing y)
                        $ comPairs vlst vlst
            dlstM = map (\ (x, y) -> mkStEq (qualThing x) $ qualThing y)
                        $ comPairs vlstM vlstM
            qVars = map thingDecl vlst
            qVarsM = map thingDecl vlstM
        oProps <- mapM (mapObjProp oprop var) vlst
        oPropsM <- mapM (mapObjProp oprop var) vlstM
        let minLst = mkExist qVars $ conjunct $ dlst ++ dOut ++ oProps
        let maxLst = mkForall qVarsM $ mkImpl (conjunct $ oPropsM ++ dOut)
                        $ disjunct dlstM
        return $ case ct of
            MinCardinality -> minLst
            MaxCardinality -> maxLst
            ExactCardinality -> conjunct [minLst, maxLst]
    DataValuesFrom ty dpe dr -> let n = var + 1 in do
        oprop0 <- mapDataProp dpe var n
        desc0 <- mapDataRange dr n
        return $ case ty of
            SomeValuesFrom -> mkExist [thingDecl n] $ conjunct [oprop0, desc0]
            AllValuesFrom -> mkForall [thingDecl n] $ mkImpl oprop0 desc0
    _ -> fail $ "could not translate " ++ show desc

mapFact :: Extended -> Fact -> Result CASLFORMULA
mapFact ex f = case f of
    ObjectPropertyFact posneg obe ind -> case ex of
        SimpleEntity (Entity NamedIndividual siri) -> do
            inS <- mapIndivURI siri
            inT <- mapIndivURI ind
            oPropH <- mapObjProp obe 1 2
            let oProp = case posneg of
                    Positive -> oPropH
                    Negative -> Negation oPropH nullRange
            return $ mkForall (map thingDecl [1, 2]) $ implConj
                            [mkEqVar (thingDecl 1) inS,
                             mkEqVar (thingDecl 2) inT] oProp
        _ -> fail $ "ObjectPropertyFactsFacts Entity fail: " ++ show f
    DataPropertyFact posneg dpe lit -> case ex of
        SimpleEntity (Entity NamedIndividual iri) -> do
            inS <- mapIndivURI iri
            inT <- mapLiteral lit
            oPropH <- mapDataProp dpe 1 2
            let oProp = case posneg of
                    Positive -> oPropH
                    Negative -> Negation oPropH nullRange
            return $ mkForall [thingDecl 1, dataDecl 2] $ implConj
                [mkEqVar (thingDecl 1) inS,
                 mkEqVar (dataDecl 2) $ upcast inT dataS] oProp
        _ -> fail $ "DataPropertyFact Entity fail " ++ show f

mapCharact :: ObjectPropertyExpression -> Character -> Result CASLFORMULA
mapCharact ope c = case c of
    Functional -> do
        so1 <- mapObjProp ope 1 2
        so2 <- mapObjProp ope 1 3
        return $ mkFIE [1, 2, 3] [so1, so2] 2 3
    InverseFunctional -> do
        so1 <- mapObjProp ope 1 3
        so2 <- mapObjProp ope 2 3
        return $ mkFIE [1, 2, 3] [so1, so2] 1 2
    Reflexive -> do
        so <- mapObjProp ope 1 1
        return $ mkRI [1] 1 so
    Irreflexive -> do
        so <- mapObjProp ope 1 1
        return $ mkRI [1] 1 $ mkNeg so
    Symmetric -> do
        so1 <- mapObjProp ope 1 2
        so2 <- mapObjProp ope 2 1
        return $ mkForall (map thingDecl [1, 2]) $ mkImpl so1 so2
    Asymmetric -> do
        so1 <- mapObjProp ope 1 2
        so2 <- mapObjProp ope 2 1
        return $ mkForall (map thingDecl [1, 2]) $ mkImpl so1 $ mkNeg so2
    Antisymmetric -> do
        so1 <- mapObjProp ope 1 2
        so2 <- mapObjProp ope 2 1
        return $ mkFIE [1, 2] [so1, so2] 1 2
    Transitive -> do
        so1 <- mapObjProp ope 1 2
        so2 <- mapObjProp ope 2 3
        so3 <- mapObjProp ope 1 3
        return $ mkForall (map thingDecl [1, 2, 3]) $ implConj [so1, so2] so3

-- | Mapping of ListFrameBit
mapListFrameBit :: Extended -> Maybe Relation -> ListFrameBit
    -> Result [CASLFORMULA]
mapListFrameBit ex rel lfb = case lfb of
    AnnotationBit _ -> return []
    ExpressionBit cls -> case ex of
          Misc _ -> return []
          SimpleEntity (Entity ty iri) -> do
              els <- mapM (\ (_, c) -> mapDescription c 1) cls             
              case ty of
                NamedIndividual | rel == Just Types -> do
                  inD <- mapIndivURI iri
                  return $ map (mkForall [thingDecl 1] . mkImpl (mkEqVar
                          (thingDecl 1) inD)) els
                DataProperty | rel == (Just $ DRRelation ADomain) -> do
                  oEx <- mapDataProp iri 1 2
                  let vars = (mkNName 1, mkNName 2)
                  return $ map (mkFEI [tokDecl (fst vars)]
                        [mkVarDecl (snd vars) dataS] oEx) els
                _ -> failMsg lfb
          ObjectEntity oe -> case rel of
              Nothing -> return []
              Just re -> case re of
                  DRRelation r -> do
                    tobjP <- mapObjProp oe 1 2
                    tdsc <- mapM (\ (_, c) -> mapDescription c $ case r of
                                ADomain -> 1
                                ARange -> 2) cls
                    let vars = case r of
                                ADomain -> (mkNName 1, mkNName 2)
                                ARange -> (mkNName 2, mkNName 1)
                    return $ map (mkFEI [tokDecl $ fst vars]
                            [tokDecl $ snd vars] tobjP) tdsc
                  _ -> failMsg lfb
          ClassEntity ce -> do
            let map2nd = map snd cls
            case rel of
              Nothing -> return []
              Just r -> case r of
                EDRelation re -> do
                    decrsS <- mapDescriptionListP 1 $ mkPairs ce map2nd
                    return $ map (\ (x, y) -> mkForall [thingDecl 1]
                            $ case re of
                                Equivalent -> mkEqv x y
                                Disjoint -> mkNeg $ conjunct [x, y]) decrsS
                SubClass -> do
                  domT <- mapDescription ce 1
                  codT <- mapDescriptionList 1 map2nd
                  return $ map (mkForall [thingDecl 1] . mkImpl domT) codT
                _ -> failMsg lfb
    ObjectBit ol ->
      let mol = fmap ObjectProp (toIRILst ObjectProperty ex)
          isJ = isJust mol
          ob = fromMaybe (error $ "could not translate " ++ show ex) mol
          map2nd = map snd ol
      in case rel of
      Nothing -> return []
      Just r -> case r of
        EDRelation ed -> do
          pairs <- mapComObjectPropsList mol map2nd 1 2
          return $ map (\ (a, b) -> mkForall (map thingDecl [1, 2]) $ case ed of
                            Equivalent -> mkEqv a b
                            Disjoint -> mkNeg $ conjunct [a, b]) pairs
        SubPropertyOf | isJ -> mapM (\ (o1, o2) ->
                    mapSubObjProp o1 o2 3) $ mkPairs ob map2nd
        InverseOf | isJ -> do
            os1 <- mapM (\ o1 -> mapObjProp o1 1 2) map2nd
            o2 <- mapObjProp ob 2 1
            return $ map (mkForall (map thingDecl [1, 2]) . mkEqv o2) os1
        _ -> return []
    DataBit db ->
      let mol = toIRILst DataProperty ex
          isJ = isJust mol
          map2nd = map snd db
          ob = fromMaybe (error $ "could not translate " ++ show ex) mol
      in case rel of
      Nothing -> return []
      Just r -> case r of
        SubPropertyOf | isJ -> do
          os1 <- mapM (\ o1 -> mapDataProp o1 1 2) map2nd
          o2 <- mapDataProp ob 2 1
          return $ map (mkForall [thingDecl 1, dataDecl 2]
                    . mkImpl o2) os1
        EDRelation ed -> do
          pairs <- mapComDataPropsList map2nd 1 2
          return $ map (\ (a, b) -> mkForall (map thingDecl [1, 2]) $ case ed of
                        Equivalent -> mkEqv a b
                        Disjoint -> mkNeg $ conjunct [a, b]) pairs
        _ -> return []
    IndividualSameOrDifferent al -> case rel of
          Nothing -> return []
          Just r -> case r of
              SDRelation re -> mapComIndivList re
                    (toIRILst NamedIndividual ex) $ map snd al
              _ -> return []
    DataPropRange dpr -> case ex of
        SimpleEntity (Entity DataProperty iri) -> do
            oEx <- mapDataProp iri 1 2
            odes <- mapM (\ (_, c) -> mapDataRange c 2) dpr
            let vars = (mkNName 1, mkNName 2)
            return $ map (mkFEI [tokDecl $ fst vars] [tokDecl $ snd vars] oEx)
                        odes
        _ -> failMsg lfb
    IndividualFacts indf -> mapM (mapFact ex . snd) indf
    ObjectCharacteristics ace -> case ex of
        ObjectEntity ope -> mapM (mapCharact ope . snd) ace
        _ -> failMsg ace

-- | Mapping of AnnFrameBit
mapAnnFrameBit :: Extended -> AnnFrameBit -> Result [CASLFORMULA]
mapAnnFrameBit ex afb =
    let err = fail $ "could not translate " ++ show afb in case afb of
    AnnotationFrameBit _ -> return []
    DataFunctional -> case ex of
        SimpleEntity (Entity _ iri) -> do
            so1 <- mapDataProp iri 1 2
            so2 <- mapDataProp iri 1 3
            return $ [mkForall (thingDecl 1 : map dataDecl [2, 3]) $ implConj
                        [so1, so2] $ mkEqVar (thingDecl 2) $ qualThing 3]
        _ -> err
    DatatypeBit dr -> case ex of
        SimpleEntity (Entity Datatype iri) -> do
            odes <- mapDataRange dr 2
            let dtb = uriToId iri
            return $ [mkForall [thingDecl 1] $ mkEqv odes $ mkMember
                    (qualThing 2) dtb]
        _ -> err
    ClassDisjointUnion clsl -> case ex of
        SimpleEntity (Entity Class iri) -> do
            decrs <- mapDescriptionList 1 clsl
            decrsS <- mapDescriptionListP 1 $ comPairs clsl clsl
            let decrsP = map (\ (x, y) -> conjunct [x, y]) decrsS
            mcls <- mapClassURI iri $ mkNName 1
            return $ [mkForall [thingDecl 1] $ mkEqv mcls $ conjunct
                    [disjunct decrs, mkNeg $ conjunct decrsP]]
        _ -> err
    ClassHasKey _ _ -> return []
    ObjectSubPropertyChain oplst ->
        mapM (\ cd -> mapSubObjPropChain oplst cd 3) oplst

mapAxioms :: Axiom -> Result [CASLFORMULA]
mapAxioms (PlainAxiom ex fb) = case fb of
    ListFrameBit rel lfb -> mapListFrameBit ex rel lfb
    AnnFrameBit _ afb -> mapAnnFrameBit ex afb
