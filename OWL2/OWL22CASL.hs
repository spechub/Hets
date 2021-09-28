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
import qualified OWL2.AS as AS
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
    AS.OntologyDocument    -- Basic spec domain
    AS.Axiom           -- sentence domain
    SymbItems       -- symbol items domain
    SymbMapItems    -- symbol map items domain
    OS.Sign         -- signature domain
    OWLMorphism     -- morphism domain
    AS.Entity          -- symbol domain
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
          preds = Map.foldWithKey (\ (AS.Entity _ ty u1) u2 -> let
              i1 = uriToCaslId u1
              i2 = uriToCaslId u2
              in case ty of
                AS.Class -> Map.insert (i1, conceptPred) i2
                AS.ObjectProperty -> Map.insert (i1, objectPropPred) i2
                AS.DataProperty -> Map.insert (i1, dataPropPred) i2
                _ -> id) Map.empty emap
          ops = Map.foldWithKey (\ (AS.Entity _ ty u1) u2 -> case ty of
                AS.NamedIndividual -> Map.insert (uriToCaslId u1, indiConst)
                  (uriToCaslId u2, Total)
                _ -> id) Map.empty emap
      return (embedMorphism () cdm ccd)
                 { op_map = ops
                 , pred_map = preds }

mapSymbol :: AS.Entity -> Set.Set Symbol
mapSymbol (AS.Entity _ ty iRi) = let
  syN = Set.singleton . Symbol (uriToCaslId iRi)
  in case ty of
    AS.Class -> syN $ PredAsItemType conceptPred
    AS.ObjectProperty -> syN $ PredAsItemType objectPropPred
    AS.DataProperty -> syN $ PredAsItemType dataPropPred
    AS.NamedIndividual -> syN $ OpAsItemType indiConst
    AS.AnnotationProperty -> Set.empty
    AS.Datatype -> Set.empty

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

mapTheory :: (OS.Sign, [Named AS.Axiom]) -> Result (CASLSign, [Named CASLFORMULA])
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
mapSentence :: Named AS.Axiom -> Result ([Named CASLFORMULA], [CASLSign])
mapSentence inSen = do
    (outAx, outSigs) <- mapAxioms $ sentence inSen
    return (map (flip mapNamed inSen . const) outAx, outSigs)

mapVar :: VarOrIndi -> Result (TERM ())
mapVar v = case v of
    OVar n -> return $ qualThing n
    OIndi i -> mapIndivURI i

-- | Mapping of Class URIs
mapClassURI :: AS.Class -> Token -> Result CASLFORMULA
mapClassURI c t = fmap (mkPred conceptPred [mkThingVar t]) $ uriToIdM c

-- | Mapping of Individual URIs
mapIndivURI :: AS.Individual -> Result (TERM ())
mapIndivURI uriI = do
    ur <- uriToIdM uriI
    return $ mkAppl (mkQualOp ur (Op_type Total [] thing nullRange)) []

mapNNInt :: AS.NNInt -> TERM ()
mapNNInt int = let AS.NNInt uInt = int in foldr1 joinDigits $ map mkDigit uInt

mapIntLit :: AS.IntLit -> TERM ()
mapIntLit int =
    let cInt = mapNNInt $ AS.absInt int
    in if AS.isNegInt int then negateInt $ upcast cInt integer
        else upcast cInt integer

mapDecLit :: AS.DecLit -> TERM ()
mapDecLit dec =
    let ip = AS.truncDec dec
        np = AS.absInt ip
        fp = AS.fracDec dec
        n = mkDecimal (mapNNInt np) (mapNNInt fp)
    in if AS.isNegInt ip then negateFloat n else n

mapFloatLit :: AS.FloatLit -> TERM ()
mapFloatLit f =
    let fb = AS.floatBase f
        ex = AS.floatExp f
     in mkFloat (mapDecLit fb) (mapIntLit ex)

mapNrLit :: AS.Literal -> TERM ()
mapNrLit l = case l of
    AS.NumberLit f
        | AS.isFloatInt f -> mapIntLit $ AS.truncDec $ AS.floatBase f
        | AS.isFloatDec f -> mapDecLit $ AS.floatBase f
        | otherwise -> mapFloatLit f
    _ -> error "not number literal"

mapLiteral :: AS.Literal -> Result (TERM ())
mapLiteral lit = return $ case lit of
    AS.Literal l ty -> Sorted_term (case ty of
        AS.Untyped _ -> foldr consChar emptyStringTerm l
        AS.Typed dt -> case AS.getDatatypeCat dt of
            AS.OWL2Number -> let p = parse literal "" l in case p of
                Right nr -> mapNrLit nr
                _ -> error "cannot parse number literal"
            AS.OWL2Bool -> case l of
                "true" -> trueT
                _ -> falseT
            _ -> foldr consChar emptyStringTerm l) dataS nullRange
    _ -> mapNrLit lit

-- | Mapping of data properties
mapDataProp :: AS.DataPropertyExpression -> Int -> Int
            -> Result CASLFORMULA
mapDataProp dp a b = fmap (mkPred dataPropPred [qualThing a, qualData b])
    $ uriToIdM dp

-- | Mapping of obj props
mapObjProp :: AS.ObjectPropertyExpression -> Int -> Int
        -> Result CASLFORMULA
mapObjProp ob a b = case ob of
      AS.ObjectProp u -> fmap (mkPred objectPropPred $ map qualThing [a, b])
            $ uriToIdM u
      AS.ObjectInverseOf u -> mapObjProp u b a

-- | Mapping of obj props with Individuals
mapObjPropI :: AS.ObjectPropertyExpression -> VarOrIndi -> VarOrIndi
              -> Result CASLFORMULA
mapObjPropI ob lP rP = case ob of
    AS.ObjectProp u -> do
        l <- mapVar lP
        r <- mapVar rP
        fmap (mkPred objectPropPred [l, r]) $ uriToIdM u
    AS.ObjectInverseOf u -> mapObjPropI u rP lP

-- | mapping of individual list
mapComIndivList :: AS.SameOrDifferent -> Maybe AS.Individual
    -> [AS.Individual] -> Result [CASLFORMULA]
mapComIndivList sod mol inds = do
    fs <- mapM mapIndivURI inds
    tps <- case mol of
        Nothing -> return $ comPairs fs fs
        Just ol -> do
            f <- mapIndivURI ol
            return $ mkPairs f fs
    return $ map (\ (x, y) -> case sod of
        AS.Same -> mkStEq x y
        AS.Different -> mkNeg $ mkStEq x y) tps

{- | Mapping along DataPropsList for creation of pairs for commutative
operations. -}
mapComDataPropsList :: Maybe AS.DataPropertyExpression
    -> [AS.DataPropertyExpression] -> Int -> Int
    -> Result [(CASLFORMULA, CASLFORMULA)]
mapComDataPropsList md props a b = do
    fs <- mapM (\ x -> mapDataProp x a b) props
    case md of
        Nothing -> return $ comPairs fs fs
        Just dp -> fmap (`mkPairs` fs) $ mapDataProp dp a b

{- | Mapping along ObjectPropsList for creation of pairs for commutative
operations. -}
mapComObjectPropsList :: Maybe AS.ObjectPropertyExpression
    -> [AS.ObjectPropertyExpression] -> Int -> Int
    -> Result [(CASLFORMULA, CASLFORMULA)]
mapComObjectPropsList mol props a b = do
    fs <- mapM (\ x -> mapObjProp x a b) props
    case mol of
        Nothing -> return $ comPairs fs fs
        Just ol -> fmap (`mkPairs` fs) $ mapObjProp ol a b

-- | mapping of Data Range
mapDataRange :: AS.DataRange -> Int -> Result (CASLFORMULA, [CASLSign])
mapDataRange dr i = case dr of
    AS.DataType d fl -> do
        let dt = mkMember (qualData i) $ uriToCaslId d 
        (sens, s) <- mapAndUnzipM (mapFacet i) fl
        return (conjunct $ dt : sens, concat s)
    AS.DataComplementOf drc -> do
        (sens, s) <- mapDataRange drc i
        return (mkNeg sens, s)
    AS.DataJunction jt drl -> do
        (jl, sl) <- mapAndUnzipM ((\ v r -> mapDataRange r v) i) drl
        --let usig = uniteL sl
        return $ case jt of
                AS.IntersectionOf -> (conjunct jl, concat sl)
                AS.UnionOf -> (disjunct jl, concat sl)
    AS.DataOneOf cs -> do
        ls <- mapM mapLiteral cs
        return (disjunct $ map (mkStEq $ qualData i) ls, [])

mkFacetPred :: TERM f -> AS.ConstrainingFacet -> Int -> (FORMULA f, Id)
mkFacetPred lit f var =
    let cf = mkInfix $ fromCF f
    in (mkPred dataPred [qualData var, lit] cf, cf)

mapFacet :: Int -> (AS.ConstrainingFacet, AS.RestrictionValue)
    -> Result (CASLFORMULA, [CASLSign])
mapFacet var (f, r) = do
    con <- mapLiteral r
    let (fp, cf) = mkFacetPred con f var
    return (fp, 
            [(emptySign ()) {predMap = MapSet.fromList [(cf, [dataPred])]}])

cardProps :: Bool
    -> Either AS.ObjectPropertyExpression AS.DataPropertyExpression -> Int
    -> [Int] -> Result [CASLFORMULA]
cardProps b prop var vLst =
    if b then let Left ope = prop in mapM (mapObjProp ope var) vLst
     else let Right dpe = prop in mapM (mapDataProp dpe var) vLst

mapCard :: Bool -> AS.CardinalityType -> Int
    -> Either AS.ObjectPropertyExpression AS.DataPropertyExpression
    -> Maybe (Either AS.ClassExpression AS.DataRange) -> Int
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
            AS.MinCardinality -> (mkExist qVars minLst, ts)
            AS.MaxCardinality -> (mkForall qVarsM maxLst, ts)
            AS.ExactCardinality -> (exactLst, ts)

-- | mapping of OWL2 Descriptions
mapDescription :: AS.ClassExpression -> Int ->
    Result (CASLFORMULA, [CASLSign])
mapDescription desc var = case desc of
    AS.Expression u -> do
        c <- mapClassURI u $ mkNName var
        return (c, [])
    AS.ObjectJunction ty ds -> do
        (els, s) <- mapAndUnzipM (flip mapDescription var) ds
        return ((case ty of
                AS.UnionOf -> disjunct
                AS.IntersectionOf -> conjunct)
            els, concat s)
    AS.ObjectComplementOf d -> do
        (els, s) <- mapDescription d var
        return (mkNeg els, s)
    AS.ObjectOneOf is -> do
        il <- mapM mapIndivURI is
        return (disjunct $ map (mkStEq $ qualThing var) il, [])
    AS.ObjectValuesFrom ty o d -> let n = var + 1 in do
        oprop0 <- mapObjProp o var n
        (desc0, s) <- mapDescription d n
        return $ case ty of
            AS.SomeValuesFrom -> (mkExist [thingDecl n] $ conjunct [oprop0, desc0],
                               s)
            AS.AllValuesFrom -> (mkVDecl [n] $ mkImpl oprop0 desc0,
                               s)
    AS.ObjectHasSelf o -> do
        op <- mapObjProp o var var
        return (op, [])
    AS.ObjectHasValue o i -> do
        op <- mapObjPropI o (OVar var) (OIndi i)
        return (op, [])
    AS.ObjectCardinality (AS.Cardinality ct n oprop d) -> mapCard True ct n
        (Left oprop) (fmap Left d) var
    AS.DataValuesFrom ty dpe dr -> let n = var + 1 in do
        oprop0 <- mapDataProp (head dpe) var n
        (desc0, s) <- mapDataRange dr n
        --let ts = niteCASLSign cSig s
        return $ case ty of
            AS.SomeValuesFrom -> (mkExist [dataDecl n] $ conjunct [oprop0, desc0],
                s)
            AS.AllValuesFrom -> (mkVDataDecl [n] $ mkImpl oprop0 desc0, s)
    AS.DataHasValue dpe c -> do
        con <- mapLiteral c
        return (mkPred dataPropPred [qualThing var, con]
                           $ uriToCaslId dpe, [])
    AS.DataCardinality (AS.Cardinality ct n dpe dr) -> mapCard False ct n
        (Right dpe) (fmap Right dr) var

-- | Mapping of a list of descriptions
mapDescriptionList :: Int -> [AS.ClassExpression]
        -> Result ([CASLFORMULA], [CASLSign])
mapDescriptionList n lst = do
    (els, s) <- mapAndUnzipM (uncurry $ mapDescription)
                    $ zip lst $ replicate (length lst) n
    return (els, concat s)

-- | Mapping of a list of pairs of descriptions
mapDescriptionListP :: Int -> [(AS.ClassExpression, AS.ClassExpression)]
                    -> Result ([(CASLFORMULA, CASLFORMULA)], [CASLSign])
mapDescriptionListP  n lst = do
    let (l, r) = unzip lst
    ([lls, rls], s) <- mapAndUnzipM (mapDescriptionList n) [l, r]
    return (zip lls rls, concat s)

-- mapFact :: Extended -> Fact -> Result CASLFORMULA
-- mapFact ex f = case f of
--     ObjectPropertyFact posneg obe ind -> case ex of
--         SimpleEntity (AS.Entity _ AS.NamedIndividual siri) -> do
--             oPropH <- mapObjPropI obe (OIndi siri) (OIndi ind)
--             let oProp = case posneg of
--                     AS.Positive -> oPropH
--                     AS.Negative -> Negation oPropH nullRange
--             return oProp
--         _ -> fail $ "ObjectPropertyFactsFacts Entity fail: " ++ show f
--     DataPropertyFact posneg dpe lit -> case ex of
--         SimpleEntity (AS.Entity _ AS.NamedIndividual iRi) -> do
--             inS <- mapIndivURI iRi
--             inT <- mapLiteral lit
--             oPropH <- mapDataProp dpe 1 2
--             let oProp = case posneg of
--                     AS.Positive -> oPropH
--                     AS.Negative -> Negation oPropH nullRange
--             return $ mkForall [thingDecl 1, dataDecl 2] $ implConj
--                 [mkEqDecl 1 inS, mkEqVar (dataDecl 2) $ upcast inT dataS] oProp
--         _ -> fail $ "DataPropertyFact Entity fail " ++ show f

mapCharact :: AS.ObjectPropertyExpression -> AS.Character
            -> Result CASLFORMULA
mapCharact ope c = case c of
    AS.Functional -> do
        so1 <- mapObjProp ope 1 2
        so2 <- mapObjProp ope 1 3
        return $ mkFIE [1, 2, 3] [so1, so2] 2 3
    AS.InverseFunctional -> do
        so1 <- mapObjProp ope 1 3
        so2 <- mapObjProp ope 2 3
        return $ mkFIE [1, 2, 3] [so1, so2] 1 2
    AS.Reflexive -> do
        so <- mapObjProp ope 1 1
        return $ mkRI [1] 1 so
    AS.Irreflexive -> do
        so <- mapObjProp ope 1 1
        return $ mkRI [1] 1 $ mkNeg so
    AS.Symmetric -> do
        so1 <- mapObjProp ope 1 2
        so2 <- mapObjProp ope 2 1
        return $ mkVDecl [1, 2] $ mkImpl so1 so2
    AS.Asymmetric -> do
        so1 <- mapObjProp ope 1 2
        so2 <- mapObjProp ope 2 1
        return $ mkVDecl [1, 2] $ mkImpl so1 $ mkNeg so2
    AS.Antisymmetric -> do
        so1 <- mapObjProp ope 1 2
        so2 <- mapObjProp ope 2 1
        return $ mkFIE [1, 2] [so1, so2] 1 2
    AS.Transitive -> do
        so1 <- mapObjProp ope 1 2
        so2 <- mapObjProp ope 2 3
        so3 <- mapObjProp ope 1 3
        return $ mkVDecl [1, 2, 3] $ implConj [so1, so2] so3

-- | Mapping of ObjectSubPropertyChain
mapSubObjPropChain :: [AS.ObjectPropertyExpression]
    -> AS.ObjectPropertyExpression -> Result CASLFORMULA
mapSubObjPropChain props oP = do
     let (_, vars) = unzip $ zip (oP:props) [1 ..]
     -- because we need n+1 vars for a chain of n roles
     oProps <- mapM (\ (z, x) -> mapObjProp z x (x+1)) $
                 zip props vars
     ooP <- mapObjProp oP 1 (head $ reverse vars)
     return $ mkVDecl vars $ implConj oProps ooP

-- | Mapping of subobj properties
mapSubObjProp :: AS.ObjectPropertyExpression
    -> AS.ObjectPropertyExpression -> Int -> Result CASLFORMULA
mapSubObjProp e1 e2 a = do
    let b = a + 1
    l <- mapObjProp e1 a b
    r <- mapObjProp e2 a b
    return $ mkForallRange (map thingDecl [a, b]) (mkImpl l r) nullRange

mkEDPairs :: [Int] -> Maybe AS.Relation -> [(FORMULA f, FORMULA f)]
    -> Result ([FORMULA f], [CASLSign])
mkEDPairs il mr pairs = do
    let ls = map (\ (x, y) -> mkVDecl il
            $ case fromMaybe (error "expected EDRelation") mr of
                AS.EDRelation AS.Equivalent -> mkEqv x y
                AS.EDRelation AS.Disjoint -> mkNC [x, y]
                _ -> error "expected EDRelation") pairs
    return (ls, [])

mkEDPairs' :: [Int] -> Maybe AS.Relation -> [(FORMULA f, FORMULA f)]
    -> Result ([FORMULA f], [CASLSign])
mkEDPairs' [i1, i2] mr pairs = do
    let ls = map (\ (x, y) -> mkVDecl [i1] $ mkVDataDecl [i2]
            $ case fromMaybe (error "expected EDRelation") mr of
                AS.EDRelation AS.Equivalent -> mkEqv x y
                AS.EDRelation AS.Disjoint -> mkNC [x, y]
                _ -> error "expected EDRelation") pairs
    return (ls, [])
mkEDPairs' _ _ _ = error "wrong call of mkEDPairs'"

-- | Mapping of ListFrameBit
-- mapListFrameBit :: Extended -> Maybe AS.Relation -> ListFrameBit
--        -> Result ([CASLFORMULA], [CASLSign])
-- mapListFrameBit ex rel lfb =
--     let err = failMsg $ PlainAxiom ex $ ListFrameBit rel lfb
--     in case lfb of
--     AnnotationBit _ -> return ([], [])
--     ExpressionBit cls -> case ex of
--           Misc _ -> let cel = map snd cls in do
--             (els, s) <- mapDescriptionListP 1 $ comPairs cel cel
--             mkEDPairs [1] rel els
--           SimpleEntity (AS.Entity _ ty iRi) -> do
--               (els, s) <- mapAndUnzipM (\ (_, c) -> mapDescription c 1) cls
--               case ty of
--                 AS.NamedIndividual | rel == Just AS.Types -> do
--                   inD <- mapIndivURI iRi
--                   let els' = map (substitute (mkNName 1) thing inD) els
--                   return ( els', concat s)
--                 AS.DataProperty | rel == (Just $ AS. DRRelation AS.ADomain) -> do
--                   oEx <- mapDataProp iRi 1 2
--                   let vars = (mkNName 1, mkNName 2)
--                   return (map (mkFI [tokDecl $ fst vars]
--                        [mkVarDecl (snd vars) dataS] oEx) els, concat s)
--                 _ -> err
--           ObjectEntity oe -> case rel of
--               Nothing -> err
--               Just re -> case re of
--                   AS.DRRelation r -> do
--                     tobjP <- mapObjProp oe 1 2
--                     (tdsc, s) <- mapAndUnzipM (\ (_, c) -> mapDescription c
--                         $ case r of
--                                 AS.ADomain -> 1
--                                 AS.ARange -> 2) cls
--                     let vars = case r of
--                                 AS.ADomain -> (mkNName 1, mkNName 2)
--                                 AS.ARange -> (mkNName 2, mkNName 1)
--                     return (map (mkFI [tokDecl $ fst vars] [tokDecl $ snd vars] tobjP) tdsc,
--                             concat s)
--                   _ -> err
--           ClassEntity ce -> let cel = map snd cls in case rel of
--               Nothing -> return ([], [])
--               Just r -> case r of
--                 AS.EDRelation _ -> do
--                     (decrsS, s) <- mapDescriptionListP 1 $ mkPairs ce cel
--                     mkEDPairs [1] rel decrsS
--                 AS.SubClass -> do
--                   (domT, s1) <- mapDescription ce 1
--                   (codT, s2) <- mapDescriptionList 1 cel
--                   return (map (mk1VDecl . mkImpl domT) codT,
--                           s1 ++ s2)
--                 _ -> err
--     ObjectBit ol -> let opl = map snd ol in case rel of
--       Nothing -> err
--       Just r -> case ex of
--         Misc _ -> do
--             pairs <- mapComObjectPropsList Nothing opl 1 2
--             mkEDPairs [1, 2] rel pairs
--         ObjectEntity op -> case r of
--             AS.EDRelation _ -> do
--                 pairs <- mapComObjectPropsList (Just op) opl 1 2
--                 mkEDPairs [1, 2] rel pairs
--             AS.SubPropertyOf -> do
--                 os <- mapM (\ (o1, o2) -> mapSubObjProp o1 o2 3)
--                     $ mkPairs op opl
--                 return (os, [])
--             AS.InverseOf -> do
--                 os1 <- mapM (\ o1 -> mapObjProp o1 1 2) opl
--                 o2 <- mapObjProp op 2 1
--                 return (map (mkVDecl [1, 2] . mkEqv o2) os1, [])
--             _ -> err
--         _ -> err
--     DataBit anl -> let dl = map snd anl in case rel of
--       Nothing -> return ([], [])
--       Just r -> case ex of
--         Misc _ -> do
--             pairs <- mapComDataPropsList Nothing dl 1 2
--             mkEDPairs' [1, 2] rel pairs
--         SimpleEntity (AS.Entity _ AS.DataProperty iRi) -> case r of
--             AS.SubPropertyOf -> do
--                 os1 <- mapM (\ o1 -> mapDataProp o1 1 2) dl
--                 o2 <- mapDataProp iRi 1 2 -- was 2 1
--                 return (map (mkForall [thingDecl 1, dataDecl 2]
--                     . mkImpl o2) os1, [])
--             AS.EDRelation _ -> do
--                 pairs <- mapComDataPropsList (Just iRi) dl 1 2
--                 mkEDPairs' [1, 2] rel pairs
--             _ -> return ([], [])
--         _ -> err
--     IndividualSameOrDifferent al -> case rel of
--         Nothing -> err
--         Just (AS.SDRelation re) -> do
--             let mi = case ex of
--                     SimpleEntity (AS.Entity _ AS.NamedIndividual iRi) -> Just iRi
--                     _ -> Nothing
--             fs <- mapComIndivList re mi $ map snd al
--             return (fs, [])
--         _ -> err
--     DataPropRange dpr -> case ex of
--         SimpleEntity (AS.Entity _ AS.DataProperty iRi) -> do
--             oEx <- mapDataProp iRi 1 2
--             (odes, s) <- mapAndUnzipM (\ (_, c) -> mapDataRange c 2) dpr
--             let vars = (mkNName 1, mkNName 2)
--             return (map (mkFEI [tokDecl $ fst vars]
--                         [tokDataDecl $ snd vars] oEx) odes, concat s)
--         _ -> err
--     IndividualFacts indf -> do
--         fl <- mapM (mapFact ex . snd) indf
--         return (fl, [])
--     ObjectCharacteristics ace -> case ex of
--         ObjectEntity ope -> do
--             cl <- mapM (mapCharact ope . snd) ace
--             return (cl, [])
--         _ -> err

-- | Mapping of AnnFrameBit
-- mapAnnFrameBit :: Extended -> Annotations -> AnnFrameBit
--             -> Result ([CASLFORMULA], [CASLSign])
-- mapAnnFrameBit ex ans afb =
--     let err = failMsg $ PlainAxiom ex $ AnnFrameBit ans afb
--     in case afb of
--     AnnotationFrameBit _ -> return ([], [])
--     DataFunctional -> case ex of
--         SimpleEntity (AS.Entity _ _ iRi) -> do
--             so1 <- mapDataProp iRi 1 2
--             so2 <- mapDataProp iRi 1 3
--             return ([mkForall (thingDecl 1 : map dataDecl [2, 3]) $ implConj
--                         [so1, so2] $ mkEqVar (dataDecl 2) $ qualData 3], [])
--         _ -> err
--     DatatypeBit dr -> case ex of
--         SimpleEntity (AS.Entity _ AS.Datatype iRi) -> do
--             (odes, s) <- mapDataRange dr 2
--             return ([mkVDataDecl [2] $ mkEqv odes $ mkMember
--                     (qualData 2) $ uriToCaslId iRi], s)
--         _ -> err
--     ClassDisjointUnion clsl -> case ex of
--         ClassEntity (AS.Expression iRi) -> do
--             (decrs, s1) <- mapDescriptionList 1 clsl
--             (decrsS, s2) <- mapDescriptionListP 1 $ comPairs clsl clsl
--             let decrsP = map (\ (x, y) -> conjunct [x, y]) decrsS
--             mcls <- mapClassURI iRi $ mkNName 1
--             return ([mk1VDecl $ mkEqv mcls $ conjunct
--                     [disjunct decrs, mkNC decrsP]], s1 ++ s2)
--         _ -> err
--     ClassHasKey opl dpl -> do
--         let ClassEntity ce  = ex
--             lo = length opl 
--             ld = length dpl
--             uptoOP = [2 .. lo + 1]
--             uptoDP = [lo + 2 .. lo + ld + 1]
--             tl = lo + ld + 2
--         ol <- mapM (\ (n, o) -> mapObjProp o 1 n) $ zip uptoOP opl
--         nol <- mapM (\ (n, o) -> mapObjProp o tl n) $ zip uptoOP opl
--         dl <- mapM (\ (n, d) -> mapDataProp d 1 n) $ zip uptoDP dpl
--         ndl <- mapM (\ (n, d) -> mapDataProp d tl n) $ zip uptoDP dpl
--         (keys, s) <-
--             mapKey ce (ol ++ dl) (nol ++ ndl) tl (uptoOP ++ uptoDP) lo
--         return ([keys], s)
--     ObjectSubPropertyChain oplst ->
--       case ex of
--        ObjectEntity oe -> do
--         os <- mapSubObjPropChain oplst oe
--         return ([os], [])
--        _ -> error "wrong annotation"
       

keyDecl :: Int -> [Int] -> [VAR_DECL]
keyDecl h il = map thingDecl (take h il) ++ map dataDecl (drop h il)

mapKey :: AS.ClassExpression -> [FORMULA ()] -> [FORMULA ()]
    -> Int -> [Int] -> Int -> Result (FORMULA (), [CASLSign])
mapKey ce pl npl p i h = do
    (nce, s) <- mapDescription ce 1
    (c3, _) <- mapDescription ce p
    let un = mkForall [thingDecl p] $ implConj (c3 : npl)
                $ mkStEq (qualThing p) $ qualThing 1
    return (mkForall [thingDecl 1] $ mkImpl nce
            $ mkExist (keyDecl h i) $ conjunct $ pl ++ [un], s)

-- mapAxioms :: AS.Axiom -> Result ([CASLFORMULA], [CASLSign])
-- mapAxioms (PlainAxiom ex fb) = case fb of
--     ListFrameBit rel lfb -> mapListFrameBit ex rel lfb
--     AnnFrameBit ans afb -> mapAnnFrameBit ex ans afb

mapAxioms :: AS.Axiom -> Result([CASLFORMULA], [CASLSign])
mapAxioms axiom = case axiom of
    AS.Declaration _ _ -> return ([], [])

    AS.ClassAxiom clAxiom -> case clAxiom of
        AS.SubClassOf _ sub sup -> do
            (domT, s1) <- mapDescription sub 1
            (codT, s2) <- mapDescriptionList 1 [sup]
            return (map (mk1VDecl . mkImpl domT) codT,
                    s1 ++ s2)
    
        AS.EquivalentClasses _ cel -> do
            (els, s) <- mapDescriptionListP 1 $ comPairs cel cel
            mkEDPairs [1] (Just $ AS.EDRelation AS.Equivalent) els

        AS.DisjointClasses _ cel -> do
            (els, s) <- mapDescriptionListP 1 $ comPairs cel cel
            mkEDPairs [1] (Just $ AS.EDRelation AS.Disjoint) els

        AS.DisjointUnion _ clIri clsl -> do
            (decrs, s1) <- mapDescriptionList 1 clsl
            (decrsS, s2) <- mapDescriptionListP 1 $ comPairs clsl clsl
            let decrsP = map (\ (x, y) -> conjunct [x, y]) decrsS
            mcls <- mapClassURI clIri $ mkNName 1
            return ([mk1VDecl $ mkEqv mcls $ conjunct
                    [disjunct decrs, mkNC decrsP]], s1 ++ s2)

    AS.ObjectPropertyAxiom opAxiom -> case opAxiom of
        AS.SubObjectPropertyOf _ subOpExpr supOpExpr -> case subOpExpr of
            AS.SubObjPropExpr_obj opExpr -> do
                os <- mapM (\ (o1, o2) -> mapSubObjProp o1 o2 3)
                    $ mkPairs opExpr [supOpExpr]
                return (os, [])
            AS.SubObjPropExpr_exprchain opExprs -> do
                os <- mapSubObjPropChain opExprs supOpExpr
                return ([os], [])

        AS.EquivalentObjectProperties _ opExprs -> do
            pairs <- mapComObjectPropsList Nothing opExprs 1 2
            mkEDPairs [1, 2] (Just $ AS.EDRelation AS.Equivalent) pairs

        AS.DisjointObjectProperties _ opExprs -> do
            pairs <- mapComObjectPropsList Nothing opExprs 1 2
            mkEDPairs [1, 2] (Just $ AS.EDRelation AS.Disjoint) pairs

        AS.InverseObjectProperties _ opExpr1 opExpr2 -> do
            os1 <- mapM (\o1 -> mapObjProp o1 1 2) [opExpr2]
            o2 <- mapObjProp opExpr1 2 1
            return (map (mkVDecl [1, 2] . mkEqv o2) os1, [])

        AS.ObjectPropertyDomain _ opExpr clExpr -> do
            tobjP <- mapObjProp opExpr 1 2
            (tdsc, s) <- mapAndUnzipM (\c -> mapDescription c 1) [clExpr]
            let vars = (mkNName 1, mkNName 2)
            return (map (mkFI [tokDecl $ fst vars] [tokDecl $ snd vars] tobjP) tdsc,
                    concat s)

        AS.ObjectPropertyRange _ opExpr clExpr -> do
            tobjP <- mapObjProp opExpr 1 2
            (tdsc, s) <- mapAndUnzipM (\c -> mapDescription c 2) [clExpr]
            let vars = (mkNName 2, mkNName 1)
            return (map (mkFI [tokDecl $ fst vars] [tokDecl $ snd vars] tobjP) tdsc,
                    concat s)

        AS.FunctionalObjectProperty _ opExpr -> do
            cl <- mapM (mapCharact opExpr) [AS.Functional]
            return (cl, [])

        AS.InverseFunctionalObjectProperty _ opExpr -> do
            cl <- mapM (mapCharact opExpr) [AS.InverseFunctional]
            return (cl, [])
            
        AS.ReflexiveObjectProperty _ opExpr -> do
            cl <- mapM (mapCharact opExpr) [AS.Reflexive]
            return (cl, [])

        AS.IrreflexiveObjectProperty _ opExpr -> do
            cl <- mapM (mapCharact opExpr) [AS.Irreflexive]
            return (cl, [])

        AS.SymmetricObjectProperty _ opExpr -> do
            cl <- mapM (mapCharact opExpr) [AS.Symmetric]
            return (cl, [])

        AS.AsymmetricObjectProperty _ opExpr -> do
            cl <- mapM (mapCharact opExpr) [AS.Asymmetric]
            return (cl, [])

        AS.TransitiveObjectProperty _ opExpr -> do
            cl <- mapM (mapCharact opExpr) [AS.Transitive]
            return (cl, [])

    AS.DataPropertyAxiom dpAxiom -> case dpAxiom of
        AS.SubDataPropertyOf _ subDpExpr supDpExpr -> do
            os1 <- mapM (\ o1 -> mapDataProp o1 1 2) [supDpExpr]
            o2 <- mapDataProp subDpExpr 1 2 -- was 2 1
            return (map (mkForall [thingDecl 1, dataDecl 2]
                . mkImpl o2) os1, [])  
        
        AS.EquivalentDataProperties _ dpExprs -> do
            pairs <- mapComDataPropsList Nothing dpExprs 1 2
            mkEDPairs' [1, 2] (Just $ AS.EDRelation AS.Equivalent) pairs

        AS.DisjointDataProperties _ dpExprs -> do
            pairs <- mapComDataPropsList Nothing dpExprs 1 2
            mkEDPairs' [1, 2] (Just $ AS.EDRelation AS.Disjoint) pairs

        AS.DataPropertyDomain _ dpExpr clExpr -> do
            (els, s) <- mapAndUnzipM (\ c -> mapDescription c 1) [clExpr]
            oEx <- mapDataProp dpExpr 1 2
            let vars = (mkNName 1, mkNName 2)
            return (map (mkFI [tokDecl $ fst vars]
                [mkVarDecl (snd vars) dataS] oEx) els, concat s)

        AS.DataPropertyRange _ dpExpr dr -> do
            oEx <- mapDataProp dpExpr 1 2
            (odes, s) <- mapAndUnzipM (\r -> mapDataRange r 2) [dr]
            let vars = (mkNName 1, mkNName 2)
            return (map (mkFEI [tokDecl $ fst vars]
                        [tokDataDecl $ snd vars] oEx) odes, concat s)

        AS.FunctionalDataProperty _ dpExpr -> do
            so1 <- mapDataProp dpExpr 1 2
            so2 <- mapDataProp dpExpr 1 3
            return ([mkForall (thingDecl 1 : map dataDecl [2, 3]) $ implConj
                        [so1, so2] $ mkEqVar (dataDecl 2) $ qualData 3], [])

    AS.DatatypeDefinition _ dt dr -> do
        (odes, s) <- mapDataRange dr 2
        return ([mkVDataDecl [2] $ mkEqv odes $ mkMember
                (qualData 2) $ uriToCaslId dt], s)

    
    AS.HasKey _ ce opl dpl -> do
        let lo = length opl 
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

    AS.Assertion axiom -> case axiom of
        AS.SameIndividual _ inds -> do
            let (mi, rest) = case inds of
                    (iri:rest) -> (Just iri, rest)
                    _ -> (Nothing, inds)
            fs <- mapComIndivList AS.Same mi rest
            return (fs, [])

        AS.DifferentIndividuals _ inds -> do
            let (mi, rest) = case inds of
                    (iri:rest) -> (Just iri, rest)
                    _ -> (Nothing, inds)
            fs <- mapComIndivList AS.Different mi inds
            return (fs, [])

        AS.ClassAssertion _ ce iIri -> do
            (els, s) <- mapAndUnzipM (\c -> mapDescription c 1) [ce]
            inD <- mapIndivURI iIri
            let els' = map (substitute (mkNName 1) thing inD) els
            return ( els', concat s)

        AS.ObjectPropertyAssertion _ op si ti -> do
            oPropH <- mapObjPropI op (OIndi si) (OIndi ti)
            return ([oPropH], [])

        AS.NegativeObjectPropertyAssertion _ op si ti -> do
            oPropH <- mapObjPropI op (OIndi si) (OIndi ti)
            let oProp = Negation oPropH nullRange
            return ([oProp], [])

        AS.DataPropertyAssertion _ dp si tv -> do
            inS <- mapIndivURI si
            inT <- mapLiteral tv
            oProp <- mapDataProp dp 1 2
            return ([mkForall [thingDecl 1, dataDecl 2] $ implConj
                [mkEqDecl 1 inS, mkEqVar (dataDecl 2) $ upcast inT dataS] oProp],
                [])

        AS.NegativeDataPropertyAssertion _ dp si tv -> do
            inS <- mapIndivURI si
            inT <- mapLiteral tv
            oPropH <- mapDataProp dp 1 2
            let oProp = Negation oPropH nullRange
            return ([mkForall [thingDecl 1, dataDecl 2] $ implConj
                [mkEqDecl 1 inS, mkEqVar (dataDecl 2) $ upcast inT dataS] oProp],
                [])

    AS.AnnotationAxiom _ -> return ([], [])

    AS.Rule axiom -> case axiom of
        AS.DLSafeRule _ b h ->
            let vars = concat $ AS.getVariablesFromAtom <$> (b ++ h)
                names = tokDecl . AS.uriToTok <$> vars
                f (sentences, sig, startVal) at = do
                    (sentences', sig', offsetValue) <- atomToSentence startVal at
                    return (sentences ++ sentences', sig ++ sig', offsetValue)

                g startVal atoms = foldM f ([], [], startVal) atoms
            in do
                (antecedentSen, sig1, offsetValue) <- g 1 b
                let antecedent = conjunct antecedentSen
                
                (consequentSen, sig2, lastVar) <- g offsetValue h
                let consequent = conjunct consequentSen

                
                let impl = mkImpl antecedent consequent
                return $ ([mkForall (names ++ map thingDecl [1..lastVar]) impl], sig1 ++ sig2)


iArgToTerm :: AS.IndividualArg -> Result(TERM ())
iArgToTerm arg = case arg of
    AS.IVar v -> return . toQualVar . tokDataDecl . AS.uriToTok $ v
    AS.IArg iri -> mapIndivURI iri

iArgToVarOrIndi :: AS.IndividualArg -> VarOrIndi
iArgToVarOrIndi arg = case arg of
    AS.IVar v -> OIndi v
    AS.IArg iri -> OIndi iri


iArgToIRI :: AS.IndividualArg -> IRI
iArgToIRI arg = case arg of
    AS.IVar var -> var
    AS.IArg ind -> ind


dArgToTerm :: AS.DataArg -> Result (TERM ())
dArgToTerm arg = case arg of
    AS.DVar var -> return . toQualVar .  tokDataDecl . AS.uriToTok $ var
    AS.DArg lit -> mapLiteral lit

atomToSentence :: Int -> AS.Atom -> Result ([CASLFORMULA], [CASLSign], Int)
atomToSentence startVar atom = case atom of
    AS.ClassAtom clExpr iarg -> do 
        (el, sigs) <- mapDescription clExpr startVar
        inD <- iArgToTerm iarg
        let el' = substitute (mkNName startVar) thing inD el
        return ([el'], sigs, startVar + 1)
        
    AS.DataRangeAtom dataRange darg -> do
        -- return ([], [], startVar)
        -- Ask mihai about it? How to represent a DataRangeAtom in CASL?
        (odes, s) <- mapDataRange dataRange startVar
        dt <- dArgToTerm darg
        return ([mkVDataDecl [startVar] $ mkEqv odes $ mkStEq (qualData startVar) dt], s, startVar + 1)

        -- forall 2: odes <=> 2 elem dt
        -- darg elem dataRange

        -- .forall 2 __dt: odes(2, ...dataRange) <=> 2 elem __dt && darg elem __dt
        -- .forall 2: odes(2, ...dataRange) <=> 2 == darg

        -- i == dataArg => i `elem` d

    AS.ObjectPropertyAtom opExpr iarg1 iarg2 -> do
        let si = iArgToVarOrIndi iarg1
            ti = iArgToVarOrIndi iarg2
        oPropH <- mapObjPropI opExpr si ti
        return ([oPropH], [], startVar)

    AS.DataPropertyAtom dpExpr iarg darg -> do
        let a = startVar
            b = startVar + 1
        inS <- iArgToTerm iarg
        inT <- dArgToTerm darg
        oProp <- mapDataProp dpExpr a b
        return ([mkForall [thingDecl a, dataDecl b] $ implConj
            [mkEqDecl a inS, mkEqVar (dataDecl b) $ upcast inT dataS] oProp],
            [], startVar + 2)

    AS.BuiltInAtom iri args -> do
        predArgs <- mapM dArgToTerm args
        let predtype = PredType $ map (const thing) args
            pred = mkPred predtype predArgs (AS.uriToId iri)

        return ([pred], [], startVar)

    AS.SameIndividualAtom iarg1 iarg2 -> do
            fs <- mapComIndivList AS.Same (Just $ iArgToIRI iarg1) [iArgToIRI iarg2]
            return (fs, [], startVar)
        
    AS.DifferentIndividualsAtom iarg1 iarg2 -> do
            fs <- mapComIndivList AS.Different (Just $ iArgToIRI iarg1) [iArgToIRI iarg2]
            return (fs, [], startVar)

    