{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  Comorphism from OWL 2 to CASL_Dl
Copyright   :  (c) Francisc-Nicolae Bungiu, Felix Gabriel Mance
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
import OWL2.Keywords
import OWL2.MS
import OWL2.AS as O
import OWL2.Parse
import OWL2.Print
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
-- import OWL2.ManchesterParser

import Common.ProofTree
import Common.DocUtils

import Data.Maybe
import Text.ParserCombinators.Parsec

import Debug.Trace

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
      map_symbol OWL22CASL = mapSymbol
      isInclusionComorphism OWL22CASL = True
      has_model_expansion OWL22CASL = True

-- s = emptySign ()

uniteL :: [CASLSign] -> CASLSign
uniteL = foldl1 uniteCASLSign

failMsg :: Pretty a => a -> Result b
failMsg a = fail $ "cannot translate: " ++ showDoc a "\n"

objectPropPred :: PredType
objectPropPred = PredType [thing, thing]

dataPropPred :: PredType
dataPropPred = PredType [thing, dataS]

indiConst :: OpType
indiConst = OpType Total [] thing

uriToIdM :: OS.Sign -> IRI -> Result Id
uriToIdM s i = return $ uriToCaslId s i 

-- | Extracts Id from URI
uriToCaslId :: OS.Sign -> IRI -> Id
uriToCaslId sig urI =
    let l = localPart urI
        ur = if isThing urI then mkQName l else urI
        repl a = if isAlphaNum a then [a] else if a/=':' then "_u" else "" 
        p = namePrefix ur
        nP = concatMap repl $ Map.findWithDefault p p $ OS.prefixMap sig   --this should be expanded always
        lP = concatMap repl l
    in stringToId $ (if isDatatypeKey urI then "" else nP) ++ lP

tokDecl :: Token -> VAR_DECL
tokDecl = flip mkVarDecl thing

tokDataDecl :: Token -> VAR_DECL
tokDataDecl = flip mkVarDecl dataS

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

mkFI :: [VAR_DECL] -> [VAR_DECL] -> FORMULA f -> FORMULA f -> FORMULA f
mkFI l1 l2 f1 f2 = mkForall l1 $ mkImpl (mkExist l2 f1) f2


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

mkVDataDecl :: [Int] -> FORMULA f -> FORMULA f
mkVDataDecl = mkForall . map dataDecl

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
      let oSig1 = osource oMor
          oSig2 = otarget oMor
      cdm <- mapSign oSig1 
      ccd <- mapSign oSig2 
      let emap = mmaps oMor
          preds = Map.foldWithKey (\ (Entity _ ty u1) u2 -> let
              i1 = uriToCaslId oSig1 u1
              i2 = uriToCaslId oSig2 u2
              in case ty of
                Class -> Map.insert (i1, conceptPred) i2
                ObjectProperty -> Map.insert (i1, objectPropPred) i2
                DataProperty -> Map.insert (i1, dataPropPred) i2
                _ -> id) Map.empty emap
          ops = Map.foldWithKey (\ (Entity _ ty u1) u2 -> case ty of
                NamedIndividual -> Map.insert (uriToCaslId oSig1 u1, indiConst)
                  (uriToCaslId oSig2 u2, Total)
                _ -> id) Map.empty emap
      return (embedMorphism () cdm ccd)
                 { op_map = ops
                 , pred_map = preds }

mapSymbol :: OS.Sign -> Entity -> Set.Set Symbol
mapSymbol oSig (Entity _ ty iri) = let
  syN = Set.singleton . Symbol (uriToCaslId oSig iri)
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
          cvrt = map (uriToCaslId sig) . Set.toList
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
        dTypes = (emptySign ()) {sortRel = Rel.transClosure . Rel.fromSet
                    . Set.map (\ d -> (uriToCaslId owlSig d, dataS))
                    . Set.union predefIRIs $ OS.datatypes owlSig}
    (cSens, nSig) <- foldM (\ (x, y) z -> do
            (sen, sig) <- mapSentence owlSig y z
            return (sen ++ x, uniteCASLSign sig y)) ([], cSig) owlSens
    return (foldl1 uniteCASLSign [nSig, pSig, dTypes],
                predefinedAxioms ++ cSens)

-- | mapping of OWL to CASL_DL formulae
mapSentence :: OS.Sign -> CASLSign -> Named Axiom -> Result ([Named CASLFORMULA], CASLSign)
mapSentence oSig cSig inSen = do
    (outAx, outSig) <- mapAxioms oSig cSig $ sentence inSen
    return (map (flip mapNamed inSen . const) outAx, outSig)

mapVar :: OS.Sign -> CASLSign -> VarOrIndi -> Result (TERM ())
mapVar oSig cSig v = case v of
    OVar n -> return $ qualThing n
    OIndi i -> mapIndivURI oSig cSig i

-- | Mapping of Class URIs
mapClassURI :: OS.Sign -> CASLSign -> Class -> Token -> Result CASLFORMULA
mapClassURI oSig _ c t = fmap (mkPred conceptPred [mkThingVar t]) $ uriToIdM oSig c

-- | Mapping of Individual URIs
mapIndivURI :: OS.Sign -> CASLSign -> Individual -> Result (TERM ())
mapIndivURI oSig _ uriI = do
    ur <- uriToIdM oSig uriI
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
        Typed dt -> case getDatatypeCat dt of
            OWL2Number -> let p = parse literal "" l in case p of
                Right nr -> mapNrLit nr
                _ -> error "cannot parse number literal"
            OWL2Bool -> case l of
                "true" -> trueT
                _ -> falseT
            _ -> foldr consChar emptyStringTerm l) dataS nullRange
    _ -> mapNrLit lit

-- | Mapping of data properties
mapDataProp :: OS.Sign -> CASLSign -> DataPropertyExpression -> Int -> Int
            -> Result CASLFORMULA
mapDataProp oSig _ dp a b = fmap (mkPred dataPropPred [qualThing a, qualData b])
    $ uriToIdM oSig dp

-- | Mapping of obj props
mapObjProp :: OS.Sign -> CASLSign -> ObjectPropertyExpression -> Int -> Int
        -> Result CASLFORMULA
mapObjProp oSig cSig ob a b = case ob of
      ObjectProp u -> fmap (mkPred objectPropPred $ map qualThing [a, b])
            $ uriToIdM oSig u
      ObjectInverseOf u -> mapObjProp oSig cSig u b a

-- | Mapping of obj props with Individuals
mapObjPropI :: OS.Sign -> CASLSign -> ObjectPropertyExpression -> VarOrIndi -> VarOrIndi
              -> Result CASLFORMULA
mapObjPropI oSig cSig ob lP rP = case ob of
    ObjectProp u -> do
        l <- mapVar oSig cSig lP
        r <- mapVar oSig cSig rP
        fmap (mkPred objectPropPred [l, r]) $ uriToIdM oSig u
    ObjectInverseOf u -> mapObjPropI oSig cSig u rP lP

-- | mapping of individual list
mapComIndivList :: OS.Sign -> CASLSign -> SameOrDifferent -> Maybe Individual
    -> [Individual] -> Result [CASLFORMULA]
mapComIndivList oSig cSig sod mol inds = do
    fs <- mapM (mapIndivURI oSig cSig) inds
    tps <- case mol of
        Nothing -> return $ comPairs fs fs
        Just ol -> do
            f <- mapIndivURI oSig cSig ol
            return $ mkPairs f fs
    return $ map (\ (x, y) -> case sod of
        Same -> mkStEq x y
        Different -> mkNeg $ mkStEq x y) tps

{- | Mapping along DataPropsList for creation of pairs for commutative
operations. -}
mapComDataPropsList :: OS.Sign -> CASLSign -> Maybe DataPropertyExpression
    -> [DataPropertyExpression] -> Int -> Int
    -> Result [(CASLFORMULA, CASLFORMULA)]
mapComDataPropsList oSig cSig md props a b = do
    fs <- mapM (\ x -> mapDataProp oSig cSig x a b) props
    case md of
        Nothing -> return $ comPairs fs fs
        Just dp -> fmap (`mkPairs` fs) $ mapDataProp oSig cSig dp a b

{- | Mapping along ObjectPropsList for creation of pairs for commutative
operations. -}
mapComObjectPropsList :: OS.Sign -> CASLSign -> Maybe ObjectPropertyExpression
    -> [ObjectPropertyExpression] -> Int -> Int
    -> Result [(CASLFORMULA, CASLFORMULA)]
mapComObjectPropsList oSig cSig mol props a b = do
    fs <- mapM (\ x -> mapObjProp oSig cSig x a b) props
    case mol of
        Nothing -> return $ comPairs fs fs
        Just ol -> fmap (`mkPairs` fs) $ mapObjProp oSig cSig ol a b

-- | mapping of Data Range
mapDataRange :: OS.Sign -> CASLSign -> DataRange -> Int -> Result (CASLFORMULA, CASLSign)
mapDataRange oSig cSig dr i = case dr of
    DataType d fl -> do
        let dt = mkMember (qualData i) $ uriToCaslId oSig d
        (sens, s) <- mapAndUnzipM (mapFacet cSig i) fl
        return (conjunct $ dt : sens, uniteL $ cSig : s)
    DataComplementOf drc -> do
        (sens, s) <- mapDataRange oSig cSig drc i
        return (mkNeg sens, uniteCASLSign cSig s)
    DataJunction jt drl -> do
        (jl, sl) <- mapAndUnzipM ((\ s v r -> mapDataRange oSig s r v) cSig i) drl
        let usig = uniteL sl
        return $ case jt of
                IntersectionOf -> (conjunct jl, usig)
                UnionOf -> (disjunct jl, usig)
    DataOneOf cs -> do
        ls <- mapM mapLiteral cs
        return (disjunct $ map (mkStEq $ qualData i) ls, cSig)

mkFacetPred :: TERM f -> ConstrainingFacet -> Int -> (FORMULA f, Id)
mkFacetPred lit f var =
    let cf = mkInfix $ fromCF f
    in (mkPred dataPred [qualData var, lit] cf, cf)

mapFacet :: CASLSign -> Int -> (ConstrainingFacet, RestrictionValue)
    -> Result (CASLFORMULA, CASLSign)
mapFacet sig var (f, r) = do
    con <- mapLiteral r
    let (fp, cf) = mkFacetPred con f var
    return (fp, uniteCASLSign sig $ (emptySign ())
            {predMap = MapSet.fromList [(cf, [dataPred])]})

cardProps :: Bool -> OS.Sign -> CASLSign
    -> Either ObjectPropertyExpression DataPropertyExpression -> Int
    -> [Int] -> Result [CASLFORMULA]
cardProps b oSig cSig prop var vLst =
    if b then let Left ope = prop in mapM (mapObjProp oSig cSig ope var) vLst
     else let Right dpe = prop in mapM (mapDataProp oSig cSig dpe var) vLst

mapCard :: Bool -> OS.Sign -> CASLSign -> CardinalityType -> Int
    -> Either ObjectPropertyExpression DataPropertyExpression
    -> Maybe (Either ClassExpression DataRange) -> Int
    -> Result (FORMULA (), CASLSign)
mapCard b oSig cSig ct n prop d var = do
    let vlst = map (var +) [1 .. n]
        vlstM = vlst ++ [n + var + 1]
    (dOut, s) <- case d of
        Nothing -> return ([], [emptySign ()])
        Just y ->
           if b then let Left ce = y in mapAndUnzipM
                        (mapDescription oSig cSig ce) vlst
           else let Right dr = y in mapAndUnzipM (mapDataRange oSig cSig dr) vlst
    let dlst = map (\ (x, y) -> mkNeg $ mkStEq (qualThing x) $ qualThing y)
                        $ comPairs vlst vlst
        dlstM = map (\ (x, y) -> mkStEq (qualThing x) $ qualThing y)
                        $ comPairs vlstM vlstM
        qVars = map thingDecl vlst
        qVarsM = map thingDecl vlstM
    oProps <- cardProps b oSig cSig prop var vlst
    oPropsM <- cardProps b oSig cSig prop var vlstM
    let minLst = mkExist qVars $ conjunct $ dlst ++ dOut ++ oProps
        maxLst = mkForall qVarsM $ mkImpl (conjunct $ oPropsM ++ dOut)
                        $ disjunct dlstM
        ts = uniteL $ cSig : s
    return $ case ct of
            MinCardinality -> (minLst, ts)
            MaxCardinality -> (maxLst, ts)
            ExactCardinality -> (conjunct [minLst, maxLst], ts)

-- | mapping of OWL2 Descriptions
mapDescription :: OS.Sign -> CASLSign -> ClassExpression -> Int ->
    Result (CASLFORMULA, CASLSign)
mapDescription oSig cSig desc var = case desc of
    Expression u -> do
        c <- mapClassURI oSig cSig u $ mkNName var
        return (c, cSig)
    ObjectJunction ty ds -> do
        (els, s) <- mapAndUnzipM (flip (mapDescription oSig cSig) var) ds
        return ((case ty of
                UnionOf -> disjunct
                IntersectionOf -> conjunct)
            els, uniteL $ cSig : s)
    ObjectComplementOf d -> do
        (els, s) <- mapDescription oSig cSig d var
        return (mkNeg els, uniteCASLSign cSig s)
    ObjectOneOf is -> do
        il <- mapM (mapIndivURI oSig cSig) is
        return (disjunct $ map (mkStEq $ qualThing var) il, cSig)
    ObjectValuesFrom ty o d -> let n = var + 1 in do
        oprop0 <- mapObjProp oSig cSig o var n
        (desc0, s) <- mapDescription oSig cSig d n
        return $ case ty of
            SomeValuesFrom -> (mkExist [thingDecl n] $ conjunct [oprop0, desc0],
                    uniteCASLSign cSig s)
            AllValuesFrom -> (mkVDecl [n] $ mkImpl oprop0 desc0,
                    uniteCASLSign cSig s)
    ObjectHasSelf o -> do
        op <- mapObjProp oSig cSig o var var
        return (op, cSig)
    ObjectHasValue o i -> do
        op <- mapObjPropI oSig cSig o (OVar var) (OIndi i)
        return (op, cSig)
    ObjectCardinality (Cardinality ct n oprop d) -> mapCard True oSig cSig ct n
        (Left oprop) (fmap Left d) var
    DataValuesFrom ty dpe dr -> let n = var + 1 in do
        oprop0 <- mapDataProp oSig cSig dpe var n
        (desc0, s) <- mapDataRange oSig cSig dr n
        let ts = uniteCASLSign cSig s
        return $ case ty of
            SomeValuesFrom -> (mkExist [dataDecl n] $ conjunct [oprop0, desc0],
                ts)
            AllValuesFrom -> (mkVDataDecl [n] $ mkImpl oprop0 desc0, ts)
    DataHasValue dpe c -> do
        con <- mapLiteral c
        return (mkPred dataPropPred [qualThing var, con]
                           $ uriToCaslId oSig dpe, cSig)
    DataCardinality (Cardinality ct n dpe dr) -> mapCard False oSig cSig ct n
        (Right dpe) (fmap Right dr) var

-- | Mapping of a list of descriptions
mapDescriptionList :: OS.Sign -> CASLSign -> Int -> [ClassExpression]
        -> Result ([CASLFORMULA], CASLSign)
mapDescriptionList oSig cSig n lst = do
    (els, s) <- mapAndUnzipM (uncurry $ mapDescription oSig cSig)
                    $ zip lst $ replicate (length lst) n
    return (els, uniteL $ cSig : s)

-- | Mapping of a list of pairs of descriptions
mapDescriptionListP :: OS.Sign -> CASLSign -> Int -> [(ClassExpression, ClassExpression)]
                    -> Result ([(CASLFORMULA, CASLFORMULA)], CASLSign)
mapDescriptionListP oSig cSig n lst = do
    let (l, r) = unzip lst
    ([lls, rls], s) <- mapAndUnzipM (mapDescriptionList oSig cSig n) [l, r]
    return (zip lls rls, uniteL $ cSig : s)

mapFact :: OS.Sign -> CASLSign -> Extended -> Fact -> Result CASLFORMULA
mapFact oSig cSig ex f = case f of
    ObjectPropertyFact posneg obe ind -> case ex of
        SimpleEntity (Entity _ NamedIndividual siri) -> do
            oPropH <- mapObjPropI oSig cSig obe (OIndi ind) (OIndi siri)
            let oProp = case posneg of
                    Positive -> oPropH
                    Negative -> Negation oPropH nullRange
            return oProp
        _ -> fail $ "ObjectPropertyFactsFacts Entity fail: " ++ show f
    DataPropertyFact posneg dpe lit -> case ex of
        SimpleEntity (Entity _ NamedIndividual iri) -> do
            inS <- mapIndivURI oSig cSig iri
            inT <- mapLiteral lit
            oPropH <- mapDataProp oSig cSig dpe 1 2
            let oProp = case posneg of
                    Positive -> oPropH
                    Negative -> Negation oPropH nullRange
            return $ mkForall [thingDecl 1, dataDecl 2] $ implConj
                [mkEqDecl 1 inS, mkEqVar (dataDecl 2) $ upcast inT dataS] oProp
        _ -> fail $ "DataPropertyFact Entity fail " ++ show f

mapCharact :: OS.Sign -> CASLSign -> ObjectPropertyExpression -> Character
            -> Result CASLFORMULA
mapCharact oSig cSig ope c = case c of
    Functional -> do
        so1 <- mapObjProp oSig cSig ope 1 2
        so2 <- mapObjProp oSig cSig ope 1 3
        return $ mkFIE [1, 2, 3] [so1, so2] 2 3
    InverseFunctional -> do
        so1 <- mapObjProp oSig cSig ope 1 3
        so2 <- mapObjProp oSig cSig ope 2 3
        return $ mkFIE [1, 2, 3] [so1, so2] 1 2
    Reflexive -> do
        so <- mapObjProp oSig cSig ope 1 1
        return $ mkRI [1] 1 so
    Irreflexive -> do
        so <- mapObjProp oSig cSig ope 1 1
        return $ mkRI [1] 1 $ mkNeg so
    Symmetric -> do
        so1 <- mapObjProp oSig cSig ope 1 2
        so2 <- mapObjProp oSig cSig ope 2 1
        return $ mkVDecl [1, 2] $ mkImpl so1 so2
    Asymmetric -> do
        so1 <- mapObjProp oSig cSig ope 1 2
        so2 <- mapObjProp oSig cSig ope 2 1
        return $ mkVDecl [1, 2] $ mkImpl so1 $ mkNeg so2
    Antisymmetric -> do
        so1 <- mapObjProp oSig cSig ope 1 2
        so2 <- mapObjProp oSig cSig ope 2 1
        return $ mkFIE [1, 2] [so1, so2] 1 2
    Transitive -> do
        so1 <- mapObjProp oSig cSig ope 1 2
        so2 <- mapObjProp oSig cSig ope 2 3
        so3 <- mapObjProp oSig cSig ope 1 3
        return $ mkVDecl [1, 2, 3] $ implConj [so1, so2] so3

-- | Mapping of ObjectSubPropertyChain
mapSubObjPropChain :: OS.Sign -> CASLSign -> [ObjectPropertyExpression]
    -> ObjectPropertyExpression -> Result CASLFORMULA
mapSubObjPropChain oSig cSig props oP = do
    let (_, vars) = unzip $ zip (oP:props) [1 ..] 
    -- because we need n+1 vars for a chain of n roles
    oProps <- mapM (\ (z, x) -> mapObjProp oSig cSig z x (x+1)) $
                zip props vars
    ooP <- mapObjProp oSig cSig oP 1 (head $ reverse vars)
    trace (show ooP) $ return $ mkVDecl vars $ implConj oProps ooP

-- | Mapping of subobj properties
mapSubObjProp :: OS.Sign -> CASLSign -> ObjectPropertyExpression
    -> ObjectPropertyExpression -> Int -> Result CASLFORMULA
mapSubObjProp oSig cSig e1 e2 a = do
    let b = a + 1
    l <- mapObjProp oSig cSig e1 a b
    r <- mapObjProp oSig cSig e2 a b
    return $ mkForallRange (map thingDecl [a, b]) (mkImpl l r) nullRange

mkEDPairs :: CASLSign -> [Int] -> Maybe O.Relation -> [(FORMULA f, FORMULA f)]
    -> Result ([FORMULA f], CASLSign)
mkEDPairs s il mr pairs = do
    let ls = map (\ (x, y) -> mkVDecl il
            $ case fromMaybe (error "expected EDRelation") mr of
                EDRelation Equivalent -> mkEqv x y
                EDRelation Disjoint -> mkNC [x, y]
                _ -> error "expected EDRelation") pairs
    return (ls, s)

-- | Mapping of ListFrameBit
mapListFrameBit :: OS.Sign -> CASLSign -> Extended -> Maybe O.Relation -> ListFrameBit
       -> Result ([CASLFORMULA], CASLSign)
mapListFrameBit oSig cSig ex rel lfb =
    let err = failMsg $ PlainAxiom ex $ ListFrameBit rel lfb
    in case lfb of
    AnnotationBit _ -> return ([], cSig)
    ExpressionBit cls -> case ex of
          Misc _ -> let cel = map snd cls in do
            (els, s) <- mapDescriptionListP oSig cSig 1 $ comPairs cel cel
            mkEDPairs (uniteCASLSign cSig s) [1] rel els
          SimpleEntity (Entity _ ty iri) -> do
              (els, s) <- mapAndUnzipM (\ (_, c) -> mapDescription oSig cSig c 1) cls
              case ty of
                NamedIndividual | rel == Just Types -> do
                  inD <- mapIndivURI oSig cSig iri
                  return (map (mk1VDecl . mkImpl (mkEqDecl 1 inD)) els,
                        uniteL $ cSig : s)
                DataProperty | rel == (Just $ DRRelation ADomain) -> do
                  oEx <- mapDataProp oSig cSig iri 1 2
                  let vars = (mkNName 1, mkNName 2)
                  return (map (mkFI [tokDecl $ fst vars]
                       [mkVarDecl (snd vars) dataS] oEx) els, uniteL $ cSig : s)
                _ -> err
          ObjectEntity oe -> case rel of
              Nothing -> err
              Just re -> case re of
                  DRRelation r -> do
                    tobjP <- mapObjProp oSig cSig oe 1 2
                    (tdsc, s) <- mapAndUnzipM (\ (_, c) -> mapDescription oSig cSig c
                        $ case r of
                                ADomain -> 1
                                ARange -> 2) cls
                    let vars = case r of
                                ADomain -> (mkNName 1, mkNName 2)
                                ARange -> (mkNName 2, mkNName 1)
                    return (map (mkFI [tokDecl $ fst vars] [tokDecl $ snd vars] tobjP) tdsc, 
                            uniteL $ cSig : s)
                  _ -> err
          ClassEntity ce -> let cel = map snd cls in case rel of
              Nothing -> return ([], cSig)
              Just r -> case r of
                EDRelation _ -> do 
                    (decrsS, s) <- mapDescriptionListP oSig cSig 1 $ mkPairs ce cel
                    mkEDPairs (uniteCASLSign cSig s) [1] rel decrsS
                SubClass -> do
                  (domT, s1) <- mapDescription oSig cSig ce 1
                  (codT, s2) <- mapDescriptionList oSig cSig 1 cel
                  return (map (mk1VDecl . mkImpl domT) codT,
                        uniteL [cSig, s1, s2])
                _ -> err
    ObjectBit ol -> let opl = map snd ol in case rel of
      Nothing -> err
      Just r -> case ex of
        Misc _ -> do
            pairs <- mapComObjectPropsList oSig cSig Nothing opl 1 2
            mkEDPairs cSig [1, 2] rel pairs
        ObjectEntity op -> case r of
            EDRelation _ -> do
                pairs <- mapComObjectPropsList oSig cSig (Just op) opl 1 2
                mkEDPairs cSig [1, 2] rel pairs
            SubPropertyOf -> do
                os <- mapM (\ (o1, o2) -> mapSubObjProp oSig cSig o1 o2 3)
                    $ mkPairs op opl
                return (os, cSig)
            InverseOf -> do
                os1 <- mapM (\ o1 -> mapObjProp oSig cSig o1 1 2) opl
                o2 <- mapObjProp oSig cSig op 2 1
                return (map (mkVDecl [1, 2] . mkEqv o2) os1, cSig)
            _ -> err
        _ -> err
    DataBit anl -> let dl = map snd anl in case rel of
      Nothing -> return ([], cSig)
      Just r -> case ex of
        Misc _ -> do
            pairs <- mapComDataPropsList oSig cSig Nothing dl 1 2
            mkEDPairs cSig [1, 2] rel pairs
        SimpleEntity (Entity _ DataProperty iri) -> case r of
            SubPropertyOf -> do
                os1 <- mapM (\ o1 -> mapDataProp oSig cSig o1 1 2) dl
                o2 <- mapDataProp oSig cSig iri 2 1
                return (map (mkForall [thingDecl 1, dataDecl 2]
                    . mkImpl o2) os1, cSig)
            EDRelation _ -> do
                pairs <- mapComDataPropsList oSig cSig (Just iri) dl 1 2
                mkEDPairs cSig [1, 2] rel pairs 
            _ -> return ([], cSig)
        _ -> err
    IndividualSameOrDifferent al -> case rel of
        Nothing -> err
        Just (SDRelation re) -> do
            let mi = case ex of
                    SimpleEntity (Entity _ NamedIndividual iri) -> Just iri
                    _ -> Nothing
            fs <- mapComIndivList oSig cSig re mi $ map snd al
            return (fs, cSig)
        _ -> err
    DataPropRange dpr -> case ex of
        SimpleEntity (Entity _ DataProperty iri) -> do
            oEx <- mapDataProp oSig cSig iri 1 2
            (odes, s) <- mapAndUnzipM (\ (_, c) -> mapDataRange oSig cSig c 2) dpr
            let vars = (mkNName 1, mkNName 2)
            return (map (mkFEI [tokDecl $ fst vars]
                        [tokDataDecl $ snd vars] oEx) odes, uniteL $ cSig : s)
        _ -> err
    IndividualFacts indf -> do
        fl <- mapM (mapFact oSig cSig ex . snd) indf
        return (fl, cSig)
    ObjectCharacteristics ace -> case ex of
        ObjectEntity ope -> do
            cl <- mapM (mapCharact oSig cSig ope . snd) ace
            return (cl, cSig)
        _ -> err

-- | Mapping of AnnFrameBit
mapAnnFrameBit :: OS.Sign -> CASLSign -> Extended -> Annotations -> AnnFrameBit
            -> Result ([CASLFORMULA], CASLSign)
mapAnnFrameBit oSig cSig ex ans afb =
    let err = failMsg $ PlainAxiom ex $ AnnFrameBit ans afb
    in case afb of
    AnnotationFrameBit _ -> return ([], cSig)
    DataFunctional -> case ex of
        SimpleEntity (Entity _ _ iri) -> do
            so1 <- mapDataProp oSig cSig iri 1 2
            so2 <- mapDataProp oSig cSig iri 1 3
            return ([mkForall (thingDecl 1 : map dataDecl [2, 3]) $ implConj
                        [so1, so2] $ mkEqVar (dataDecl 2) $ qualData 3], cSig)
        _ -> err
    DatatypeBit dr -> case ex of
        SimpleEntity (Entity _ Datatype iri) -> do
            (odes, s) <- mapDataRange oSig cSig dr 2
            return ([mkVDataDecl [2] $ mkEqv odes $ mkMember
                    (qualData 2) $ uriToCaslId oSig iri], uniteCASLSign cSig s)
        _ -> err
    ClassDisjointUnion clsl -> case ex of
        ClassEntity (Expression iri) -> do
            (decrs, s1) <- mapDescriptionList oSig cSig 1 clsl
            (decrsS, s2) <- mapDescriptionListP oSig cSig 1 $ comPairs clsl clsl
            let decrsP = map (\ (x, y) -> conjunct [x, y]) decrsS
            mcls <- mapClassURI oSig cSig iri $ mkNName 1
            return ([mk1VDecl $ mkEqv mcls $ conjunct
                    [disjunct decrs, mkNC decrsP]], uniteL [cSig, s1, s2])
        _ -> err
    ClassHasKey opl dpl -> do
        let ClassEntity ce = ex
            lo = length opl
            ld = length dpl
            uptoOP = [2 .. lo + 1]
            uptoDP = [lo + 2 .. lo + ld + 1]
            tl = lo + ld + 2
        ol <- mapM (\ (n, o) -> mapObjProp oSig cSig o 1 n) $ zip uptoOP opl
        nol <- mapM (\ (n, o) -> mapObjProp oSig cSig o tl n) $ zip uptoOP opl
        dl <- mapM (\ (n, d) -> mapDataProp oSig cSig d 1 n) $ zip uptoDP dpl
        ndl <- mapM (\ (n, d) -> mapDataProp oSig cSig d tl n) $ zip uptoDP dpl
        (keys, s) <-
            mapKey oSig cSig ce (ol ++ dl) (nol ++ ndl) tl (uptoOP ++ uptoDP) lo
        return ([keys], uniteCASLSign cSig s)
    ObjectSubPropertyChain oplst -> 
      case ex of 
       ObjectEntity oe -> do
        os <- mapSubObjPropChain oSig cSig oplst oe
        return ([os], cSig)
       _ -> error "wrong annotation"

keyDecl :: Int -> [Int] -> [VAR_DECL]
keyDecl h il = map thingDecl (take h il) ++ map dataDecl (drop h il)

mapKey :: OS.Sign -> CASLSign -> ClassExpression -> [FORMULA ()] -> [FORMULA ()]
    -> Int -> [Int] -> Int -> Result (FORMULA (), CASLSign)
mapKey oSig cSig ce pl npl p i h = do
    (nce, s) <- mapDescription oSig cSig ce 1
    (c3, _) <- mapDescription oSig cSig ce p
    let un = mkForall [thingDecl p] $ implConj (c3 : npl)
                $ mkStEq (qualThing p) $ qualThing 1
    return (mkForall [thingDecl 1] $ mkImpl nce
            $ mkExist (keyDecl h i) $ conjunct $ pl ++ [un], s)

mapAxioms :: OS.Sign -> CASLSign -> Axiom -> Result ([CASLFORMULA], CASLSign)
mapAxioms oSig cSig (PlainAxiom ex fb) = case fb of
    ListFrameBit rel lfb -> mapListFrameBit oSig cSig ex rel lfb
    AnnFrameBit ans afb -> mapAnnFrameBit oSig cSig ex ans afb
