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
-- import OWL2.Parse
-- import OWL2.ManchesterParser
-- import Text.ParserCombinators.Parsec

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

--s = emptySign ()

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

mkNC :: [FORMULA f] -> FORMULA f
mkNC = mkNeg . conjunct

mkEqVar :: VAR_DECL -> TERM f -> FORMULA f
mkEqVar = mkStEq . toQualVar

mkFEI :: [VAR_DECL] -> [VAR_DECL] -> FORMULA f -> FORMULA f -> FORMULA f
mkFEI l1 l2 f = mkForall l1 . mkExist l2 . mkImpl f

mkFIE :: [Int] -> [FORMULA f] -> Int -> Int -> FORMULA f
mkFIE l1 l2 x y = mkVDecl l1 $ implConj l2 $ mkEqVar (thingDecl x) $ qualThing y

mkRI :: [Int] -> Int -> FORMULA f -> FORMULA f
mkRI l x so = mkVDecl l $ mkImpl (mkMember (qualThing x) thing) so

mkThingVar :: VAR -> TERM f
mkThingVar v = Qual_var v thing nullRange

mkEqDecl :: Int -> TERM f -> FORMULA f
mkEqDecl i = mkEqVar (thingDecl i)

mkVDecl :: [Int] -> FORMULA f -> FORMULA f
mkVDecl = mkForall . map thingDecl

mk1VDecl :: FORMULA f -> FORMULA f
mk1VDecl = mkVDecl [1]

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

mapSign :: OS.Sign -> Result CASLSign
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

mapTheory :: (OS.Sign, [Named Axiom]) -> Result (CASLSign, [Named CASLFORMULA])
mapTheory (owlSig, owlSens) = let sl = topS in do
    cSig <- mapSign owlSig
    let pSig = loadDataInformation sl
    (cSens, nSig) <- foldM (\ (x, y) z -> do
            (sen, sig) <- mapSentence y z
            return (sen ++ x, uniteCASLSign sig y)) ([], cSig) owlSens
    return (uniteCASLSign nSig pSig, predefinedAxioms ++ cSens)

-- | mapping of OWL to CASL_DL formulae
mapSentence :: CASLSign -> Named Axiom -> Result ([Named CASLFORMULA], CASLSign)
mapSentence cSig inSen = do
    (outAx, outSig) <- mapAxioms cSig $ sentence inSen
    return (map (flip mapNamed inSen . const) outAx, outSig)

mapVar :: CASLSign -> VarOrIndi -> Result (TERM ())
mapVar cSig v = case v of
    OVar n -> return $ qualThing n
    OIndi i -> mapIndivURI cSig i

-- | Mapping of Class URIs
mapClassURI :: CASLSign -> Class -> Token -> Result CASLFORMULA
mapClassURI _ c t = fmap (mkPred conceptPred [mkThingVar t]) $ uriToIdM c

-- | Mapping of Individual URIs
mapIndivURI :: CASLSign -> Individual -> Result (TERM ())
mapIndivURI _ uriI = do
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

-- | Mapping of data properties
mapDataProp :: CASLSign -> DataPropertyExpression -> Int -> Int
            -> Result CASLFORMULA
mapDataProp _ dp a b = fmap (mkPred dataPropPred [qualThing a, qualData b])
    $ uriToIdM dp

-- | Mapping of obj props
mapObjProp :: CASLSign -> ObjectPropertyExpression -> Int -> Int
        -> Result CASLFORMULA
mapObjProp cSig ob a b = case ob of
      ObjectProp u -> fmap (mkPred objectPropPred $ map qualThing [a, b])
            $ uriToIdM u
      ObjectInverseOf u -> mapObjProp cSig u b a

-- | Mapping of obj props with Individuals
mapObjPropI :: CASLSign -> ObjectPropertyExpression -> VarOrIndi -> VarOrIndi
              -> Result CASLFORMULA
mapObjPropI cSig ob lP rP = case ob of
    ObjectProp u -> do
        l <- mapVar cSig lP
        r <- mapVar cSig rP
        fmap (mkPred objectPropPred [l, r]) $ uriToIdM u
    ObjectInverseOf u -> mapObjPropI cSig u rP lP

-- | mapping of individual list
mapComIndivList :: CASLSign -> SameOrDifferent -> Maybe Individual
    -> [Individual] -> Result [CASLFORMULA]
mapComIndivList cSig sod mol inds = do
    fs <- mapM (mapIndivURI cSig) inds
    tps <- case mol of
        Nothing -> return $ comPairs fs fs
        Just ol -> do
            f <- mapIndivURI cSig ol
            return $ mkPairs f fs
    return $ map (\ (x, y) -> case sod of
        Same -> mkStEq x y
        Different -> mkNeg $ mkStEq x y) tps

{- | Mapping along DataPropsList for creation of pairs for commutative
operations. -}
mapComDataPropsList :: CASLSign -> Maybe DataPropertyExpression
    -> [DataPropertyExpression] -> Int -> Int
    -> Result [(CASLFORMULA, CASLFORMULA)]
mapComDataPropsList cSig md props a b = do
    fs <- mapM (\ x -> mapDataProp cSig x a b) props
    case md of
        Nothing -> return $ comPairs fs fs
        Just dp -> fmap (`mkPairs` fs) $ mapDataProp cSig dp a b

{- | Mapping along ObjectPropsList for creation of pairs for commutative
operations. -}
mapComObjectPropsList :: CASLSign -> Maybe ObjectPropertyExpression
    -> [ObjectPropertyExpression] -> Int -> Int
    -> Result [(CASLFORMULA, CASLFORMULA)]
mapComObjectPropsList cSig mol props a b = do
    fs <- mapM (\ x -> mapObjProp cSig x a b) props
    case mol of
        Nothing -> return $ comPairs fs fs
        Just ol -> fmap (`mkPairs` fs) $ mapObjProp cSig ol a b

-- | mapping of Data Range
mapDataRange :: CASLSign -> DataRange -> Int -> Result CASLFORMULA
mapDataRange cSig dr i = case dr of
    DataType d _ -> fmap (mkMember $ qualThing i) $ uriToIdM d
    DataComplementOf drc -> fmap mkNeg $ mapDataRange cSig drc i
    _ -> fail $ "could not translate " ++ show dr

-- | mapping of OWL2 Descriptions
mapDescription :: CASLSign -> ClassExpression -> Int -> Result CASLFORMULA
mapDescription cSig desc var = case desc of
    Expression u -> mapClassURI cSig u $ mkNName var
    ObjectJunction ty ds -> fmap (case ty of
                UnionOf -> disjunct
                IntersectionOf -> conjunct)
            $ mapM (flip (mapDescription cSig) var) ds
    ObjectComplementOf d -> fmap mkNeg $ mapDescription cSig d var
    ObjectOneOf is -> fmap (disjunct . map (mkStEq $ qualThing var))
            $ mapM (mapIndivURI cSig) is
    ObjectValuesFrom ty o d -> let n = var + 1 in do
        oprop0 <- mapObjProp cSig o var n
        desc0 <- mapDescription cSig d n
        return $ case ty of
            SomeValuesFrom -> mkExist [thingDecl n] $ conjunct [oprop0, desc0]
            AllValuesFrom -> mkVDecl [n] $ mkImpl oprop0 desc0
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
    DataValuesFrom ty dpe dr -> let n = var + 1 in do
        oprop0 <- mapDataProp cSig dpe var n
        desc0 <- mapDataRange cSig dr n
        return $ case ty of
            SomeValuesFrom -> mkExist [thingDecl n] $ conjunct [oprop0, desc0]
            AllValuesFrom -> mkVDecl [n] $ mkImpl oprop0 desc0
    _ -> fail $ "could not translate " ++ show desc

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
    [lls, rls] <- mapM (mapDescriptionList cSig n) [l, r]
    return $ zip lls rls

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
            return $ mkVDecl [1, 2] $ implConj
                            [mkEqDecl 1 inS, mkEqDecl 2 inT] oProp
        _ -> fail $ "ObjectPropertyFactsFacts Entity fail: " ++ show f
    DataPropertyFact posneg dpe lit -> case ex of
        SimpleEntity (Entity NamedIndividual iri) -> do
            inS <- mapIndivURI cSig iri
            inT <- mapLiteral lit
            oPropH <- mapDataProp cSig dpe 1 2
            let oProp = case posneg of
                    Positive -> oPropH
                    Negative -> Negation oPropH nullRange
            return $ mkForall [thingDecl 1, dataDecl 2] $ implConj
                [mkEqDecl 1 inS, mkEqVar (dataDecl 2) $ upcast inT dataS] oProp
        _ -> fail $ "DataPropertyFact Entity fail " ++ show f

mapCharact :: CASLSign -> ObjectPropertyExpression -> Character
            -> Result CASLFORMULA
mapCharact cSig ope c = case c of
    Functional -> do
        so1 <- mapObjProp cSig ope 1 2
        so2 <- mapObjProp cSig ope 1 3
        return $ mkFIE [1, 2, 3] [so1, so2] 2 3
    InverseFunctional -> do
        so1 <- mapObjProp cSig ope 1 3
        so2 <- mapObjProp cSig ope 2 3
        return $ mkFIE [1, 2, 3] [so1, so2] 1 2
    Reflexive -> do
        so <- mapObjProp cSig ope 1 1
        return $ mkRI [1] 1 so
    Irreflexive -> do
        so <- mapObjProp cSig ope 1 1
        return $ mkRI [1] 1 $ mkNeg so
    Symmetric -> do
        so1 <- mapObjProp cSig ope 1 2
        so2 <- mapObjProp cSig ope 2 1
        return $ mkVDecl [1, 2] $ mkImpl so1 so2
    Asymmetric -> do
        so1 <- mapObjProp cSig ope 1 2
        so2 <- mapObjProp cSig ope 2 1
        return $ mkVDecl [1, 2] $ mkImpl so1 $ mkNeg so2
    Antisymmetric -> do
        so1 <- mapObjProp cSig ope 1 2
        so2 <- mapObjProp cSig ope 2 1
        return $ mkFIE [1, 2] [so1, so2] 1 2
    Transitive -> do
        so1 <- mapObjProp cSig ope 1 2
        so2 <- mapObjProp cSig ope 2 3
        so3 <- mapObjProp cSig ope 1 3
        return $ mkVDecl [1, 2, 3] $ implConj [so1, so2] so3

-- | Mapping of ObjectSubPropertyChain
mapSubObjPropChain :: CASLSign -> [ObjectPropertyExpression]
    -> ObjectPropertyExpression -> Int -> Result CASLFORMULA
mapSubObjPropChain cSig props oP n = let m = n + 1 in do
    let (_, vars) = unzip $ zip (tail props) [m + 1 ..]
        vl = n : vars ++ [m]
    oProps <- mapM (\ (z, x, y) -> mapObjProp cSig z x y) $
                zip3 props vl $ tail vl
    ooP <- mapObjProp cSig oP n m
    return $ mkVDecl [1, 2] $ mkVDecl vars $ implConj oProps ooP

-- | Mapping of subobj properties
mapSubObjProp :: CASLSign -> ObjectPropertyExpression
    -> ObjectPropertyExpression -> Int -> Result CASLFORMULA
mapSubObjProp cSig e1 e2 a = do
    let b = a + 1
    l <- mapObjProp cSig e1 a b
    r <- mapObjProp cSig e2 a b
    return $ mkForallRange (map thingDecl [a, b]) (mkImpl r l ) nullRange

mkEDPairs :: CASLSign -> [Int] -> Maybe Relation -> [(FORMULA f, FORMULA f)]
    -> Result ([FORMULA f], CASLSign)
mkEDPairs s il mr pairs = do
    let ls = map (\ (x, y) -> mkVDecl il
            $ case fromMaybe (error "expected EDRelation") mr of
                EDRelation Equivalent -> mkEqv x y
                EDRelation Disjoint -> mkNC [x, y]
                _ -> error "expected EDRelation") pairs
    return (ls, s)

-- | Mapping of ListFrameBit
mapListFrameBit :: CASLSign -> Extended -> Maybe Relation -> ListFrameBit
       -> Result ([CASLFORMULA], CASLSign)
mapListFrameBit cSig ex rel lfb = case lfb of
    AnnotationBit _ -> return ([], cSig)
    ExpressionBit cls -> case ex of
          Misc _ -> let cel = map snd cls in do
            els <- mapDescriptionListP cSig 1 $ comPairs cel cel
            mkEDPairs cSig [1] rel els
          SimpleEntity (Entity ty iri) -> do
              els <- mapM (\ (_, c) -> mapDescription cSig c 1) cls
              case ty of
                NamedIndividual | rel == Just Types -> do
                  inD <- mapIndivURI cSig iri
                  return (map (mk1VDecl . mkImpl (mkEqDecl 1 inD)) els, cSig)
                DataProperty | rel == (Just $ DRRelation ADomain) -> do
                  oEx <- mapDataProp cSig iri 1 2
                  let vars = (mkNName 1, mkNName 2)
                  return (map (mkFEI [tokDecl $ fst vars]
                        [mkVarDecl (snd vars) dataS] oEx) els, cSig)
                _ -> failMsg lfb
          ObjectEntity oe -> case rel of
              Nothing -> failMsg lfb
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
          ClassEntity ce -> let cel = map snd cls in case rel of
              Nothing -> return ([], cSig)
              Just r -> case r of
                EDRelation _ -> do
                    decrsS <- mapDescriptionListP cSig 1 $ mkPairs ce cel
                    mkEDPairs cSig [1] rel decrsS
                SubClass -> do
                  domT <- mapDescription cSig ce 1
                  codT <- mapDescriptionList cSig 1 cel
                  return (map (mk1VDecl . mkImpl domT) codT, cSig)
                _ -> failMsg lfb
    ObjectBit ol -> let opl = map snd ol in case rel of
      Nothing -> failMsg lfb
      Just r -> case ex of
        Misc _ -> do
            pairs <- mapComObjectPropsList cSig Nothing opl 1 2
            mkEDPairs cSig [1, 2] rel pairs
        ObjectEntity op -> case r of
            EDRelation _ -> do
                pairs <- mapComObjectPropsList cSig (Just op) opl 1 2
                mkEDPairs cSig [1, 2] rel pairs
            SubPropertyOf -> do
                os <- mapM (\ (o1, o2) -> mapSubObjProp cSig o1 o2 3)
                    $ mkPairs op opl
                return (os, cSig)
            InverseOf -> do
                os1 <- mapM (\ o1 -> mapObjProp cSig o1 1 2) opl
                o2 <- mapObjProp cSig op 2 1
                return (map (mkVDecl [1, 2] . mkEqv o2) os1, cSig)
            _ -> failMsg lfb
        _ -> failMsg lfb
    DataBit anl -> let dl = map snd anl in case rel of
      Nothing -> return ([], cSig)
      Just r -> case ex of
        Misc _ -> do
            pairs <- mapComDataPropsList cSig Nothing dl 1 2
            mkEDPairs cSig [1, 2] rel pairs
        SimpleEntity (Entity DataProperty iri) -> case r of
            SubPropertyOf -> do
                os1 <- mapM (\ o1 -> mapDataProp cSig o1 1 2) dl
                o2 <- mapDataProp cSig iri 2 1
                return (map (mkForall [thingDecl 1, dataDecl 2]
                    . mkImpl o2) os1, cSig)
            EDRelation _ -> do
                pairs <- mapComDataPropsList cSig (Just iri) dl 1 2
                mkEDPairs cSig [1, 2] rel pairs
            _ -> return ([], cSig)
        _ -> failMsg lfb
    IndividualSameOrDifferent al -> case rel of
        Nothing -> failMsg lfb
        Just (SDRelation re) -> do
            let SimpleEntity (Entity NamedIndividual iri) = ex
            fs <- mapComIndivList cSig re (Just iri) $ map snd al
            return (fs, cSig)
        _ -> failMsg lfb
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
            return ([mk1VDecl $ mkEqv odes $ mkMember
                    (qualThing 2) $ uriToId iri], cSig)
        _ -> err
    ClassDisjointUnion clsl -> case ex of
        SimpleEntity (Entity Class iri) -> do
            decrs <- mapDescriptionList cSig 1 clsl
            decrsS <- mapDescriptionListP cSig 1 $ comPairs clsl clsl
            let decrsP = map (\ (x, y) -> conjunct [x, y]) decrsS
            mcls <- mapClassURI cSig iri $ mkNName 1
            return ([mk1VDecl $ mkEqv mcls $ conjunct
                    [disjunct decrs, mkNC decrsP]], cSig)
        _ -> err
    ClassHasKey opl dpl -> do
        let ClassEntity ce = ex
            lo = length opl
            ld = length dpl
            uptoOP = [2 .. lo + 1]
            uptoDP = [lo + 2 .. lo + ld + 1]
            tl = lo + ld + 2
        ol <- mapM (\ (n, o) -> mapObjProp cSig o 1 n) $ zip uptoOP opl
        nol <- mapM (\ (n, o) -> mapObjProp cSig o tl n) $ zip uptoOP opl
        dl <- mapM (\ (n, d) -> mapDataProp cSig d 1 n) $ zip uptoDP dpl
        ndl <- mapM (\ (n, d) -> mapDataProp cSig d tl n) $ zip uptoDP dpl
        keys <- mapKey cSig ce (ol ++ dl, nol ++ ndl) tl
                    $ uptoOP ++ uptoDP
        return ([keys], cSig)
    ObjectSubPropertyChain oplst -> do
        os <- mapM (\ cd -> mapSubObjPropChain cSig oplst cd 3) oplst
        return (os, cSig)

mapKey :: CASLSign -> ClassExpression -> ([FORMULA ()], [FORMULA ()])
    -> Int -> [Int] -> Result (FORMULA ())
mapKey cSig ce (pl, npl) p i = do
    nce <- mapDescription cSig ce 1
    c3 <- mapDescription cSig ce p
    let un = mkForall [thingDecl p] $ implConj (c3 : npl)
                $ mkStEq (qualThing p) $ qualThing 1
    return $ mkForall [thingDecl 1] $ mkImpl nce
            $ mkExist (map thingDecl i) $ conjunct $ pl ++ [un]

mapAxioms :: CASLSign -> Axiom -> Result ([CASLFORMULA], CASLSign)
mapAxioms cSig (PlainAxiom ex fb) = case fb of
    ListFrameBit rel lfb -> mapListFrameBit cSig ex rel lfb
    AnnFrameBit _ afb -> mapAnnFrameBit cSig ex afb
