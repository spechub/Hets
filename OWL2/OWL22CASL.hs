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
import Common.IRI
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
import qualified OWL2.Sublogic as SL
-- CASL_DL = codomain
import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism
import CASL.Induction
import CASL.Sublogic
-- import OWL2.ManchesterParser

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


uriToIdM :: IRI -> Result Id
uriToIdM = return . uriToCaslId

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

mkFIE :: [Int] -> [FORMULA f] -> Int -> Int -> FORMULA f
mkFIE l1 l2 x y = mkVDecl l1 $ implConj l2 $ mkEqVar (thingDecl x) $ qualThing y

mkFI :: [VAR_DECL] -> [VAR_DECL] -> FORMULA f -> FORMULA f -> FORMULA f
mkFI l1 l2 f1 = (mkForall l1) . (mkImpl (mkExist l2 f1))

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
      cdm <- mapSign $ osource oMor
      ccd <- mapSign $ otarget oMor
      let emap = mmaps oMor
          preds = Map.foldWithKey (\ (Entity _ ty u1) u2 -> let
              i1 = uriToCaslId u1
              i2 = uriToCaslId u2
              in case ty of
                Class -> Map.insert (i1, conceptPred) i2
                ObjectProperty -> Map.insert (i1, objectPropPred) i2
                DataProperty -> Map.insert (i1, dataPropPred) i2
                _ -> id) Map.empty emap
          ops = Map.foldWithKey (\ (Entity _ ty u1) u2 -> case ty of
                NamedIndividual -> Map.insert (uriToCaslId u1, indiConst)
                  (uriToCaslId u2, Total)
                _ -> id) Map.empty emap
      return (embedMorphism () cdm ccd)
                 { op_map = ops
                 , pred_map = preds }

mapSymbol :: Entity -> Set.Set Symbol
mapSymbol (Entity _ ty iRi) = let
  syN = Set.singleton . Symbol (uriToCaslId iRi)
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
          cvrt = map uriToCaslId . Set.toList
          tMp k = MapSet.fromList . map (\ u -> (u, [k]))
          cPreds = thing : nothing : cvrt conc
          oPreds = cvrt $ OS.objectProperties sig
          dPreds = cvrt $ OS.dataProperties sig
          aPreds = foldr MapSet.union MapSet.empty
            [ tMp conceptPred cPreds
            , tMp objectPropPred oPreds
            , tMp dataPropPred dPreds ]
     in return $  uniteCASLSign predefSign2
         (emptySign ())
             { predMap = aPreds
             , opMap = tMp indiConst . cvrt $ OS.individuals sig
             }

loadDataInformation :: ProfSub -> CASLSign
loadDataInformation sl = let
  dts = Set.map uriToCaslId $ SL.datatype $ sublogic sl
  eSig x = (emptySign ()) { sortRel =
       Rel.fromList  [(x, dataS)]}
  sigs = Set.toList $
         Set.map (\x -> Map.findWithDefault (eSig x) x datatypeSigns) dts
 in  foldl uniteCASLSign (emptySign ()) sigs

mapTheory :: (OS.Sign, [Named Axiom]) -> Result (CASLSign, [Named CASLFORMULA])
mapTheory (owlSig, owlSens) = let
  sl = sublogicOfTheo OWL2 (owlSig, map sentence owlSens)
 in do
    cSig <- mapSign owlSig
    let pSig = loadDataInformation sl
        {- dTypes = (emptySign ()) {sortRel = Rel.transClosure . Rel.fromSet
                    . Set.map (\ d -> (uriToCaslId d, dataS))
                    . Set.union predefIRIs $ OS.datatypes owlSig} -}
    (cSens, nSigs) <- foldM (\ (x, y) z -> do
            (sen, y') <- mapSentence z
            return (sen ++ x, y ++ y')) -- uniteCASLSign sig y)) 
                     ([], []) owlSens
    return (foldl1 uniteCASLSign $ [cSig,pSig] ++ nSigs,  -- , dTypes],
            predefinedAxioms ++ (reverse cSens))

-- | mapping of OWL to CASL_DL formulae
mapSentence :: Named Axiom -> Result ([Named CASLFORMULA], [CASLSign])
mapSentence inSen = do
    (outAx, outSigs) <- mapAxioms $ sentence inSen
    return (map (flip mapNamed inSen . const) outAx, outSigs)

mapVar :: VarOrIndi -> Result (TERM ())
mapVar v = case v of
    OVar n -> return $ qualThing n
    OIndi i -> mapIndivURI i

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
mapDataProp :: DataPropertyExpression -> Int -> Int
            -> Result CASLFORMULA
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
        l <- mapVar lP
        r <- mapVar rP
        fmap (mkPred objectPropPred [l, r]) $ uriToIdM u
    ObjectInverseOf u -> mapObjPropI u rP lP

-- | mapping of individual list
mapComIndivList :: SameOrDifferent -> Maybe Individual
    -> [Individual] -> Result [CASLFORMULA]
mapComIndivList sod mol inds = do
    fs <- mapM mapIndivURI inds
    tps <- case mol of
        Nothing -> return $ comPairs fs fs
        Just ol -> do
            f <- mapIndivURI ol
            return $ mkPairs f fs
    return $ map (\ (x, y) -> case sod of
        Same -> mkStEq x y
        Different -> mkNeg $ mkStEq x y) tps

{- | Mapping along DataPropsList for creation of pairs for commutative
operations. -}
mapComDataPropsList :: Maybe DataPropertyExpression
    -> [DataPropertyExpression] -> Int -> Int
    -> Result [(CASLFORMULA, CASLFORMULA)]
mapComDataPropsList md props a b = do
    fs <- mapM (\ x -> mapDataProp x a b) props
    case md of
        Nothing -> return $ comPairs fs fs
        Just dp -> fmap (`mkPairs` fs) $ mapDataProp dp a b

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

-- | mapping of Data Range
mapDataRange :: DataRange -> Int -> Result (CASLFORMULA, [CASLSign])
mapDataRange dr i = case dr of
    DataType d fl -> do
        let dt = mkMember (qualData i) $ uriToCaslId d
        (sens, s) <- mapAndUnzipM (mapFacet i) fl
        return (conjunct $ dt : sens, concat s)
    DataComplementOf drc -> do
        (sens, s) <- mapDataRange drc i
        return (mkNeg sens, s)
    DataJunction jt drl -> do
        (jl, sl) <- mapAndUnzipM ((\ v r -> mapDataRange r v) i) drl
        --let usig = uniteL sl
        return $ case jt of
                IntersectionOf -> (conjunct jl, concat sl)
                UnionOf -> (disjunct jl, concat sl)
    DataOneOf cs -> do
        ls <- mapM mapLiteral cs
        return (disjunct $ map (mkStEq $ qualData i) ls, [])

mkFacetPred :: TERM f -> ConstrainingFacet -> Int -> (FORMULA f, Id)
mkFacetPred lit f var =
    let cf = mkInfix $ fromCF f
    in (mkPred dataPred [qualData var, lit] cf, cf)

mapFacet :: Int -> (ConstrainingFacet, RestrictionValue)
    -> Result (CASLFORMULA, [CASLSign])
mapFacet var (f, r) = do
    con <- mapLiteral r
    let (fp, cf) = mkFacetPred con f var
    return (fp, 
            [(emptySign ()) {predMap = MapSet.fromList [(cf, [dataPred])]}])

cardProps :: Bool
    -> Either ObjectPropertyExpression DataPropertyExpression -> Int
    -> [Int] -> Result [CASLFORMULA]
cardProps b prop var vLst =
    if b then let Left ope = prop in mapM (mapObjProp ope var) vLst
     else let Right dpe = prop in mapM (mapDataProp dpe var) vLst

mapCard :: Bool -> CardinalityType -> Int
    -> Either ObjectPropertyExpression DataPropertyExpression
    -> Maybe (Either ClassExpression DataRange) -> Int
    -> Result (FORMULA (), [CASLSign])
mapCard b ct n prop d var = do
    let vlst = map (var +) [1 .. n]
        vlstM = vlst ++ [n + var + 1]
        vlstE = [n + var + 1]
    (dOut, s) <- case d of
        Nothing -> return ([], [])
        Just y ->
           if b then let Left ce = y in mapAndUnzipM
                        (mapDescription ce) vlst
           else let Right dr = y in mapAndUnzipM (mapDataRange dr) vlst
    (eOut, s') <- case d of
        Nothing -> return ([], [])
        Just y ->
           if b then let Left ce = y in mapAndUnzipM
                        (mapDescription ce) vlstM
           else let Right dr = y in mapAndUnzipM (mapDataRange dr) vlstM
    (fOut, s'') <- case d of
        Nothing -> return ([], [])
        Just y ->
           if b then let Left ce = y in mapAndUnzipM
                        (mapDescription ce) vlstE
           else let Right dr = y in mapAndUnzipM (mapDataRange dr) vlstE
    let dlst = map (\ (x, y) -> mkNeg $ mkStEq (qualThing x) $ qualThing y)
                        $ comPairs vlst vlst
        dlstM = map (\ (x, y) -> mkStEq (qualThing x) $ qualThing y)
                        $ comPairs vlstM vlstM
        qVars = map thingDecl vlst
        qVarsM = map thingDecl vlstM
        qVarsE = map thingDecl vlstE
    oProps <- cardProps b prop var vlst
    oPropsM <- cardProps b prop var vlstM
    oPropsE <- cardProps b prop var vlstE
    let minLst = conjunct $ dlst ++ oProps ++ dOut
        maxLst = mkImpl (conjunct $ oPropsM ++ eOut)
                        $ disjunct dlstM
        exactLst' = mkImpl (conjunct $ oPropsE ++ fOut) $ disjunct dlstM
        senAux = conjunct [minLst, mkForall qVarsE exactLst']
        exactLst =  if null qVars then senAux else mkExist qVars senAux
        ts = concat $ s ++ s' ++ s''
    return $ case ct of
            MinCardinality -> (mkExist qVars minLst, ts)
            MaxCardinality -> (mkForall qVarsM maxLst, ts)
            ExactCardinality -> (exactLst, ts)

-- | mapping of OWL2 Descriptions
mapDescription :: ClassExpression -> Int ->
    Result (CASLFORMULA, [CASLSign])
mapDescription desc var = case desc of
    Expression u -> do
        c <- mapClassURI u $ mkNName var
        return (c, [])
    ObjectJunction ty ds -> do
        (els, s) <- mapAndUnzipM (flip mapDescription var) ds
        return ((case ty of
                UnionOf -> disjunct
                IntersectionOf -> conjunct)
            els, concat s)
    ObjectComplementOf d -> do
        (els, s) <- mapDescription d var
        return (mkNeg els, s)
    ObjectOneOf is -> do
        il <- mapM mapIndivURI is
        return (disjunct $ map (mkStEq $ qualThing var) il, [])
    ObjectValuesFrom ty o d -> let n = var + 1 in do
        oprop0 <- mapObjProp o var n
        (desc0, s) <- mapDescription d n
        return $ case ty of
            SomeValuesFrom -> (mkExist [thingDecl n] $ conjunct [oprop0, desc0],
                               s)
            AllValuesFrom -> (mkVDecl [n] $ mkImpl oprop0 desc0,
                               s)
    ObjectHasSelf o -> do
        op <- mapObjProp o var var
        return (op, [])
    ObjectHasValue o i -> do
        op <- mapObjPropI o (OVar var) (OIndi i)
        return (op, [])
    ObjectCardinality (Cardinality ct n oprop d) -> mapCard True ct n
        (Left oprop) (fmap Left d) var
    DataValuesFrom ty dpe dr -> let n = var + 1 in do
        oprop0 <- mapDataProp dpe var n
        (desc0, s) <- mapDataRange dr n
        --let ts = niteCASLSign cSig s
        return $ case ty of
            SomeValuesFrom -> (mkExist [dataDecl n] $ conjunct [oprop0, desc0],
                s)
            AllValuesFrom -> (mkVDataDecl [n] $ mkImpl oprop0 desc0, s)
    DataHasValue dpe c -> do
        con <- mapLiteral c
        return (mkPred dataPropPred [qualThing var, con]
                           $ uriToCaslId dpe, [])
    DataCardinality (Cardinality ct n dpe dr) -> mapCard False ct n
        (Right dpe) (fmap Right dr) var

-- | Mapping of a list of descriptions
mapDescriptionList :: Int -> [ClassExpression]
        -> Result ([CASLFORMULA], [CASLSign])
mapDescriptionList n lst = do
    (els, s) <- mapAndUnzipM (uncurry $ mapDescription)
                    $ zip lst $ replicate (length lst) n
    return (els, concat s)

-- | Mapping of a list of pairs of descriptions
mapDescriptionListP :: Int -> [(ClassExpression, ClassExpression)]
                    -> Result ([(CASLFORMULA, CASLFORMULA)], [CASLSign])
mapDescriptionListP  n lst = do
    let (l, r) = unzip lst
    ([lls, rls], s) <- mapAndUnzipM (mapDescriptionList n) [l, r]
    return (zip lls rls, concat s)

mapFact :: Extended -> Fact -> Result CASLFORMULA
mapFact ex f = case f of
    ObjectPropertyFact posneg obe ind -> case ex of
        SimpleEntity (Entity _ NamedIndividual siri) -> do
            oPropH <- mapObjPropI obe (OIndi siri) (OIndi ind)
            let oProp = case posneg of
                    Positive -> oPropH
                    Negative -> Negation oPropH nullRange
            return oProp
        _ -> fail $ "ObjectPropertyFactsFacts Entity fail: " ++ show f
    DataPropertyFact posneg dpe lit -> case ex of
        SimpleEntity (Entity _ NamedIndividual iRi) -> do
            inS <- mapIndivURI iRi
            inT <- mapLiteral lit
            oPropH <- mapDataProp dpe 1 2
            let oProp = case posneg of
                    Positive -> oPropH
                    Negative -> Negation oPropH nullRange
            return $ mkForall [thingDecl 1, dataDecl 2] $ implConj
                [mkEqDecl 1 inS, mkEqVar (dataDecl 2) $ upcast inT dataS] oProp
        _ -> fail $ "DataPropertyFact Entity fail " ++ show f

mapCharact :: ObjectPropertyExpression -> Character
            -> Result CASLFORMULA
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
        return $ mkVDecl [1, 2] $ mkImpl so1 so2
    Asymmetric -> do
        so1 <- mapObjProp ope 1 2
        so2 <- mapObjProp ope 2 1
        return $ mkVDecl [1, 2] $ mkImpl so1 $ mkNeg so2
    Antisymmetric -> do
        so1 <- mapObjProp ope 1 2
        so2 <- mapObjProp ope 2 1
        return $ mkFIE [1, 2] [so1, so2] 1 2
    Transitive -> do
        so1 <- mapObjProp ope 1 2
        so2 <- mapObjProp ope 2 3
        so3 <- mapObjProp ope 1 3
        return $ mkVDecl [1, 2, 3] $ implConj [so1, so2] so3

-- | Mapping of ObjectSubPropertyChain
mapSubObjPropChain :: [ObjectPropertyExpression]
    -> ObjectPropertyExpression -> Result CASLFORMULA
mapSubObjPropChain props oP = do
     let (_, vars) = unzip $ zip (oP:props) [1 ..]
     -- because we need n+1 vars for a chain of n roles
     oProps <- mapM (\ (z, x) -> mapObjProp z x (x+1)) $
                 zip props vars
     ooP <- mapObjProp oP 1 (head $ reverse vars)
     return $ mkVDecl vars $ implConj oProps ooP

-- | Mapping of subobj properties
mapSubObjProp :: ObjectPropertyExpression
    -> ObjectPropertyExpression -> Int -> Result CASLFORMULA
mapSubObjProp e1 e2 a = do
    let b = a + 1
    l <- mapObjProp e1 a b
    r <- mapObjProp e2 a b
    return $ mkForallRange (map thingDecl [a, b]) (mkImpl l r) nullRange

mkEDPairs :: [Int] -> Maybe O.Relation -> [(FORMULA f, FORMULA f)]
    -> Result ([FORMULA f], [CASLSign])
mkEDPairs il mr pairs = do
    let ls = map (\ (x, y) -> mkVDecl il
            $ case fromMaybe (error "expected EDRelation") mr of
                EDRelation Equivalent -> mkEqv x y
                EDRelation Disjoint -> mkNC [x, y]
                _ -> error "expected EDRelation") pairs
    return (ls, [])

mkEDPairs' :: [Int] -> Maybe O.Relation -> [(FORMULA f, FORMULA f)]
    -> Result ([FORMULA f], [CASLSign])
mkEDPairs' [i1, i2] mr pairs = do
    let ls = map (\ (x, y) -> mkVDecl [i1] $ mkVDataDecl [i2]
            $ case fromMaybe (error "expected EDRelation") mr of
                EDRelation Equivalent -> mkEqv x y
                EDRelation Disjoint -> mkNC [x, y]
                _ -> error "expected EDRelation") pairs
    return (ls, [])
mkEDPairs' _ _ _ = error "wrong call of mkEDPairs'"

-- | Mapping of ListFrameBit
mapListFrameBit :: Extended -> Maybe O.Relation -> ListFrameBit
       -> Result ([CASLFORMULA], [CASLSign])
mapListFrameBit ex rel lfb =
    let err = failMsg $ PlainAxiom ex $ ListFrameBit rel lfb
    in case lfb of
    AnnotationBit _ -> return ([], [])
    ExpressionBit cls -> case ex of
          Misc _ -> let cel = map snd cls in do
            (els, s) <- mapDescriptionListP 1 $ comPairs cel cel
            mkEDPairs [1] rel els
          SimpleEntity (Entity _ ty iRi) -> do
              (els, s) <- mapAndUnzipM (\ (_, c) -> mapDescription c 1) cls
              case ty of
                NamedIndividual | rel == Just Types -> do
                  inD <- mapIndivURI iRi
                  let els' = map (substitute (mkNName 1) thing inD) els
                  return ( els', concat s)
                DataProperty | rel == (Just $ DRRelation ADomain) -> do
                  oEx <- mapDataProp iRi 1 2
                  let vars = (mkNName 1, mkNName 2)
                  return (map (mkFI [tokDecl $ fst vars]
                       [mkVarDecl (snd vars) dataS] oEx) els, concat s)
                _ -> err
          ObjectEntity oe -> case rel of
              Nothing -> err
              Just re -> case re of
                  DRRelation r -> do
                    tobjP <- mapObjProp oe 1 2
                    (tdsc, s) <- mapAndUnzipM (\ (_, c) -> mapDescription c
                        $ case r of
                                ADomain -> 1
                                ARange -> 2) cls
                    let vars = case r of
                                ADomain -> (mkNName 1, mkNName 2)
                                ARange -> (mkNName 2, mkNName 1)
                    return (map (mkFI [tokDecl $ fst vars] [tokDecl $ snd vars] tobjP) tdsc,
                            concat s)
                  _ -> err
          ClassEntity ce -> let cel = map snd cls in case rel of
              Nothing -> return ([], [])
              Just r -> case r of
                EDRelation _ -> do
                    (decrsS, s) <- mapDescriptionListP 1 $ mkPairs ce cel
                    mkEDPairs [1] rel decrsS
                SubClass -> do
                  (domT, s1) <- mapDescription ce 1
                  (codT, s2) <- mapDescriptionList 1 cel
                  return (map (mk1VDecl . mkImpl domT) codT,
                          s1 ++ s2)
                _ -> err
    ObjectBit ol -> let opl = map snd ol in case rel of
      Nothing -> err
      Just r -> case ex of
        Misc _ -> do
            pairs <- mapComObjectPropsList Nothing opl 1 2
            mkEDPairs [1, 2] rel pairs
        ObjectEntity op -> case r of
            EDRelation _ -> do
                pairs <- mapComObjectPropsList (Just op) opl 1 2
                mkEDPairs [1, 2] rel pairs
            SubPropertyOf -> do
                os <- mapM (\ (o1, o2) -> mapSubObjProp o1 o2 3)
                    $ mkPairs op opl
                return (os, [])
            InverseOf -> do
                os1 <- mapM (\ o1 -> mapObjProp o1 1 2) opl
                o2 <- mapObjProp op 2 1
                return (map (mkVDecl [1, 2] . mkEqv o2) os1, [])
            _ -> err
        _ -> err
    DataBit anl -> let dl = map snd anl in case rel of
      Nothing -> return ([], [])
      Just r -> case ex of
        Misc _ -> do
            pairs <- mapComDataPropsList Nothing dl 1 2
            mkEDPairs' [1, 2] rel pairs
        SimpleEntity (Entity _ DataProperty iRi) -> case r of
            SubPropertyOf -> do
                os1 <- mapM (\ o1 -> mapDataProp o1 1 2) dl
                o2 <- mapDataProp iRi 1 2 -- was 2 1
                return (map (mkForall [thingDecl 1, dataDecl 2]
                    . mkImpl o2) os1, [])
            EDRelation _ -> do
                pairs <- mapComDataPropsList (Just iRi) dl 1 2
                mkEDPairs' [1, 2] rel pairs
            _ -> return ([], [])
        _ -> err
    IndividualSameOrDifferent al -> case rel of
        Nothing -> err
        Just (SDRelation re) -> do
            let mi = case ex of
                    SimpleEntity (Entity _ NamedIndividual iRi) -> Just iRi
                    _ -> Nothing
            fs <- mapComIndivList re mi $ map snd al
            return (fs, [])
        _ -> err
    DataPropRange dpr -> case ex of
        SimpleEntity (Entity _ DataProperty iRi) -> do
            oEx <- mapDataProp iRi 1 2
            (odes, s) <- mapAndUnzipM (\ (_, c) -> mapDataRange c 2) dpr
            let vars = (mkNName 1, mkNName 2)
            return (map (mkFEI [tokDecl $ fst vars]
                        [tokDataDecl $ snd vars] oEx) odes, concat s)
        _ -> err
    IndividualFacts indf -> do
        fl <- mapM (mapFact ex . snd) indf
        return (fl, [])
    ObjectCharacteristics ace -> case ex of
        ObjectEntity ope -> do
            cl <- mapM (mapCharact ope . snd) ace
            return (cl, [])
        _ -> err

-- | Mapping of AnnFrameBit
mapAnnFrameBit :: Extended -> Annotations -> AnnFrameBit
            -> Result ([CASLFORMULA], [CASLSign])
mapAnnFrameBit ex ans afb =
    let err = failMsg $ PlainAxiom ex $ AnnFrameBit ans afb
    in case afb of
    AnnotationFrameBit _ -> return ([], [])
    DataFunctional -> case ex of
        SimpleEntity (Entity _ _ iRi) -> do
            so1 <- mapDataProp iRi 1 2
            so2 <- mapDataProp iRi 1 3
            return ([mkForall (thingDecl 1 : map dataDecl [2, 3]) $ implConj
                        [so1, so2] $ mkEqVar (dataDecl 2) $ qualData 3], [])
        _ -> err
    DatatypeBit dr -> case ex of
        SimpleEntity (Entity _ Datatype iRi) -> do
            (odes, s) <- mapDataRange dr 2
            return ([mkVDataDecl [2] $ mkEqv odes $ mkMember
                    (qualData 2) $ uriToCaslId iRi], s)
        _ -> err
    ClassDisjointUnion clsl -> case ex of
        ClassEntity (Expression iRi) -> do
            (decrs, s1) <- mapDescriptionList 1 clsl
            (decrsS, s2) <- mapDescriptionListP 1 $ comPairs clsl clsl
            let decrsP = map (\ (x, y) -> conjunct [x, y]) decrsS
            mcls <- mapClassURI iRi $ mkNName 1
            return ([mk1VDecl $ mkEqv mcls $ conjunct
                    [disjunct decrs, mkNC decrsP]], s1 ++ s2)
        _ -> err
    ClassHasKey opl dpl -> do
        let ClassEntity ce = ex
            lo = length opl
            ld = length dpl
            uptoOP = [2 .. lo + 1]
            uptoDP = [lo + 2 .. lo + ld + 1]
            tl = lo + ld + 2
        ol <- mapM (\ (n, o) -> mapObjProp o 1 n) $ zip uptoOP opl
        nol <- mapM (\ (n, o) -> mapObjProp o tl n) $ zip uptoOP opl
        dl <- mapM (\ (n, d) -> mapDataProp d 1 n) $ zip uptoDP dpl
        ndl <- mapM (\ (n, d) -> mapDataProp d tl n) $ zip uptoDP dpl
        (keys, s) <-
            mapKey ce (ol ++ dl) (nol ++ ndl) tl (uptoOP ++ uptoDP) lo
        return ([keys], s)
    ObjectSubPropertyChain oplst ->
      case ex of
       ObjectEntity oe -> do
        os <- mapSubObjPropChain oplst oe
        return ([os], [])
       _ -> error "wrong annotation"

keyDecl :: Int -> [Int] -> [VAR_DECL]
keyDecl h il = map thingDecl (take h il) ++ map dataDecl (drop h il)

mapKey :: ClassExpression -> [FORMULA ()] -> [FORMULA ()]
    -> Int -> [Int] -> Int -> Result (FORMULA (), [CASLSign])
mapKey ce pl npl p i h = do
    (nce, s) <- mapDescription ce 1
    (c3, _) <- mapDescription ce p
    let un = mkForall [thingDecl p] $ implConj (c3 : npl)
                $ mkStEq (qualThing p) $ qualThing 1
    return (mkForall [thingDecl 1] $ mkImpl nce
            $ mkExist (keyDecl h i) $ conjunct $ pl ++ [un], s)

mapAxioms :: Axiom -> Result ([CASLFORMULA], [CASLSign])
mapAxioms (PlainAxiom ex fb) = case fb of
    ListFrameBit rel lfb -> mapListFrameBit ex rel lfb
    AnnFrameBit ans afb -> mapAnnFrameBit ex ans afb
