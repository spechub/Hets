{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  ./OWL2/OWL22CommonLogic.hs
Description :  Comorphism from OWL2 to Common Logic
Copyright   :  (c) Francisc-Nicolae Bungiu, Felix Gabriel Mance
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
import Data.Either
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.Map as Map

-- OWL2 = domain
import OWL2.Logic_OWL2
import OWL2.AS
import Common.IRI
import OWL2.Keywords
import OWL2.ProfilesAndSublogics
import OWL2.Morphism
import OWL2.Symbols hiding (idToRaw)
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
    TEXT_META               -- sentence codomain
    SYMB_ITEMS              -- symbol items codomain
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
      -- map_theory is not needed when mapMarkedTheory is defined
      map_theory OWL22CommonLogic = error "map_theory OWL22CommonLogic"
      mapMarkedTheory OWL22CommonLogic = mapTheory
      map_morphism OWL22CommonLogic = mapMorphism
      map_symbol OWL22CommonLogic _ = mapSymbol
      isInclusionComorphism OWL22CommonLogic = True
      has_model_expansion OWL22CommonLogic = True

-- s = emptySig

smap :: Monad m =>
        (t4 -> t -> t1 -> t2 -> m t3) -> t4 -> t -> t1 -> t2 -> m (t3, t4)
smap f s a b c = do
    x <- f s a b c
    return (x, s)

hetsPrefix :: String
hetsPrefix = ""

voiToTok :: VarOrIndi -> Token
voiToTok v = case v of
    OVar o -> mkNName o
    OIndi o -> uriToTok o

varToInt :: VarOrIndi -> Int
varToInt v = case v of
    OVar i -> i
    _ -> error $ "could not translate " ++ show v

uriToTokM :: IRI -> Result Token
uriToTokM = return . uriToTok

mkBools :: BOOL_SENT -> SENTENCE
mkBools bs = Bool_sent bs nullRange

mkAtoms :: ATOM -> SENTENCE
mkAtoms as = Atom_sent as nullRange

mkUnivQ :: [NAME_OR_SEQMARK] -> SENTENCE -> Id.Range -> SENTENCE
mkUnivQ = Quant_sent Universal

mkExist :: [NAME_OR_SEQMARK] -> SENTENCE -> Id.Range -> SENTENCE
mkExist = Quant_sent Existential

cnjct :: [SENTENCE] -> BOOL_SENT
cnjct = Junction Conjunction

dsjct :: [SENTENCE] -> BOOL_SENT
dsjct = Junction Disjunction

mkNeg :: SENTENCE -> BOOL_SENT
mkNeg = Negation

mkImpl :: SENTENCE -> SENTENCE -> BOOL_SENT
mkImpl = BinOp Implication

mkBicnd :: SENTENCE -> SENTENCE -> BOOL_SENT
mkBicnd = BinOp Biconditional

mkNAME :: Int -> NAME_OR_SEQMARK
mkNAME n = Name (mkNName n)

mkNTERM :: Int -> TERM
mkNTERM n = Name_term (mkNName n)

mkVTerm :: VarOrIndi -> TERM
mkVTerm = Name_term . voiToTok

mkTermSeq :: NAME -> TERM_SEQ
mkTermSeq = Term_seq . Name_term

senToText :: SENTENCE -> TEXT
senToText s = Text [Sentence s] nullRange

msen2Txt :: [SENTENCE] -> [TEXT]
msen2Txt = map senToText

mk1NTERM :: TERM
mk1NTERM = mkNTERM 1

mk1NAME :: NAME_OR_SEQMARK
mk1NAME = mkNAME 1

mk1QU :: SENTENCE -> SENTENCE
mk1QU s = mkUnivQ [mk1NAME] s nullRange

mkQU :: [NAME_OR_SEQMARK] -> SENTENCE -> SENTENCE
mkQU l s = mkUnivQ l s nullRange

mkBI :: SENTENCE -> SENTENCE -> SENTENCE
mkBI s = mkBools . mkImpl s

mkBN :: SENTENCE -> SENTENCE
mkBN = mkBools . mkNeg

mkBD :: [SENTENCE] -> SENTENCE
mkBD sl = case sl of
    [s] -> s
    _ -> mkBools $ dsjct sl

mkBC :: [SENTENCE] -> SENTENCE
mkBC sl = case sl of
    [s] -> s
    _ -> mkBools $ cnjct sl

mkBB :: SENTENCE -> SENTENCE -> SENTENCE
mkBB s = mkBools . mkBicnd s

mkQE :: [NAME_OR_SEQMARK] -> SENTENCE -> SENTENCE
mkQE l s = mkExist l s nullRange

mkAE :: TERM -> TERM -> SENTENCE
mkAE t = mkAtoms . Equation t

mkEqual :: NAME -> NAME -> SENTENCE
mkEqual t1 t2 = mkAE (Name_term t1) $ Name_term t2

mkSent :: [NAME_OR_SEQMARK] -> [NAME_OR_SEQMARK] -> SENTENCE -> SENTENCE
       -> SENTENCE
mkSent l1 l2 s = mkQU l1 . mkQE l2 . mkBI s

mkQUBI :: [NAME_OR_SEQMARK] -> [SENTENCE] -> TERM -> TERM -> TEXT
mkQUBI l1 l2 a b = senToText $ mkQU l1 $ mkBI (mkBC l2) $ mkAE a b

mkTermAtoms :: NAME -> [TERM] -> SENTENCE
mkTermAtoms ur tl = mkAtoms $ Atom (Name_term ur) $ map Term_seq tl

mk1TermAtom :: NAME -> SENTENCE
mk1TermAtom ur = mkTermAtoms ur [mk1NTERM]

mkSAtom :: String -> SENTENCE
mkSAtom = mk1TermAtom . mkSimpleId

sHead :: [SENTENCE] -> SENTENCE
sHead s = case s of
    [a] -> a
    _ -> mkBC s

eqFB :: [Int] -> [SENTENCE] -> TEXT
eqFB nl l = senToText $ mkQU (map mkNAME nl) $ sHead l

mkNNameH :: Int -> String
mkNNameH k = case k of
    0 -> ""
    j -> mkNNameH (j `div` 26) ++ [chr $ j `mod` 26 + 96]

-- | Build a name
mkNName :: Int -> Token
mkNName i = mkSimpleId $ hetsPrefix ++ mkNNameH i

-- | Get all distinct pairs for commutative operations
comPairs :: [t] -> [t1] -> [(t, t1)]
comPairs [] [] = []
comPairs _ [] = []
comPairs [] _ = []
comPairs (a : as) (_ : bs) = mkPairs a bs ++ comPairs as bs

mkPairs :: t -> [t1] -> [(t, t1)]
mkPairs a = map (\ b -> (a, b))

data VarOrIndi = OVar Int | OIndi IRI
    deriving Show

-- | Mapping of OWL morphisms to CommonLogic morphisms
mapMorphism :: OWLMorphism -> Result CLM.Morphism
mapMorphism oMor = do
    dm <- mapSign $ osource oMor
    cd <- mapSign $ otarget oMor
    mapp <- mapMap $ mmaps oMor
    return (CLM.mkMorphism dm cd mapp)

mapMap :: Map.Map Entity IRI -> Result (Map.Map Id Id)
mapMap m = return $ Map.map uriToId $ Map.mapKeys entityToId m

mapSymbol :: Entity -> Set.Set Symbol
mapSymbol (Entity _ _ iri) = Set.singleton $ idToRaw $ uriToId iri

mapSign :: OS.Sign -> Result Sign
mapSign sig =
  let conc = Set.unions [ OS.concepts sig
                        , OS.datatypes sig
                        , OS.objectProperties sig
                        , OS.dataProperties sig
                        , OS.annotationRoles sig
                        , OS.individuals sig ]
      itms = Set.map uriToId conc
  in return emptySig { discourseNames = itms }

nothingSent :: CommonAnno.Named TEXT
nothingSent = CommonAnno.makeNamed "" $ senToText $ mk1QU $ mkBN $ mkSAtom
    "Nothing"

thingIncl :: IRI -> CommonAnno.Named TEXT
thingIncl iri = CommonAnno.makeNamed "" $ senToText
    $ mk1QU $ mkBI (mk1TermAtom $ uriToTok iri) $ mkSAtom "Thing"

dataIncl :: IRI -> CommonAnno.Named TEXT
dataIncl iri = CommonAnno.makeNamed "" $ senToText
    $ mk1QU $ mkBI (mk1TermAtom $ uriToTok iri) $ mkSAtom "Datatype"

propertyIncl :: String -> IRI -> CommonAnno.Named TEXT
propertyIncl s prop = CommonAnno.makeNamed "" $ senToText $
    let [d, pr] = map (`mkTermAtoms` map mkNTERM [1, 2])
            [uriToTok prop, mkSimpleId s]
    in mkBI d $ if s `elem` [topDataProp, topObjProp] then pr else mkBN pr

declarations :: OS.Sign -> [CommonAnno.Named TEXT]
declarations s =
    let c = Set.toList $ OS.concepts s
        dt = Set.toList $ OS.datatypes s
        dp = Set.toList $ OS.dataProperties s
        op = Set.toList $ OS.objectProperties s
    in map thingIncl c
        ++ map dataIncl (map (mkAbbrevIRI "xsd") datatypeKeys ++ dt)
        ++ map (propertyIncl topDataProp) dp
        ++ map (propertyIncl bottomDataProp) dp
        ++ map (propertyIncl topObjProp) op
        ++ map (propertyIncl bottomObjProp) op

thingDataDisjoint :: CommonAnno.Named TEXT
thingDataDisjoint = CommonAnno.makeNamed "" $ senToText $ mk1QU $ mkBN
    $ mkBC $ map mkSAtom ["Thing", "Datatype"]

mapTheory :: (OS.Sign, [CommonAnno.Named Axiom])
             -> Result (Sign, [CommonAnno.Named TEXT_META])
mapTheory (owlSig, owlSens) = do
    cSig <- mapSign owlSig
    (cSensI, nSig) <- foldM (\ (x, y) z ->
              do
                (sen, sig) <- mapSentence y z
                return (x ++ sen, unite sig y)
                ) ([], cSig) owlSens
    let sig = unite (emptySig {discourseNames = Set.fromList $ map (uriToId .
            setReservedPrefix . mkIRI) $ "Datatype" : predefClass
            ++ [topDataProp, bottomDataProp, topObjProp, bottomObjProp]
            ++ datatypeKeys}) nSig
        cSens = map (CommonAnno.markSen "OWLbuiltin")
                  [nothingSent, thingDataDisjoint]
                ++ map (CommonAnno.markSen "OWLsign") (declarations owlSig)
                ++ map (CommonAnno.markSen "OWLsen") cSensI
    return (sig, map (CommonAnno.mapNamed addMrs) cSens)

-- | mapping of OWL to CommonLogic_DL formulae
mapSentence :: Sign                             -- ^ CommonLogic Signature
  -> CommonAnno.Named Axiom                     -- ^ OWL2 Sentence
  -> Result ([CommonAnno.Named TEXT], Sign)     -- ^ CommonLogic TEXT
mapSentence cSig inSen = do
    (outAx, outSig) <- mapAxioms cSig $ CommonAnno.sentence inSen
    return (map (flip CommonAnno.mapNamed inSen . const) outAx, outSig)

-- | Mapping of Class IRIs
mapClassIRI :: Sign -> Class -> Token -> Result SENTENCE
mapClassIRI _ c tok = fmap (`mkTermAtoms` [Name_term tok]) $ uriToTokM c

-- | Mapping of Individual IRIs
mapIndivIRI :: Sign -> Individual -> Result TERM
mapIndivIRI _ i = fmap Name_term $ uriToTokM i

-- | mapping of individual list
mapComIndivList :: Sign -> SameOrDifferent -> Maybe Individual -> [Individual]
                -> Result [SENTENCE]
mapComIndivList cSig sod mi inds = do
    fs <- mapM (mapIndivIRI cSig) inds
    il <- case mi of
        Nothing -> return $ comPairs fs fs
        Just i -> fmap (`mkPairs` fs) $ mapIndivIRI cSig i
    let sntLst = map (\ (x, y) -> case sod of
                    Same -> mkAE x y
                    Different -> mkBN $ mkAE x y) il
    return [mkBC sntLst]

mapLitAux :: VarOrIndi -> Literal -> Result (Either (SENTENCE, SENTENCE) TERM)
mapLitAux var c = return $ case c of
    Literal l ty -> case ty of
        Typed dt -> Left (mkEqual (mkSimpleId l) $ voiToTok var,
                    mkTermAtoms (uriToTok dt) [mkVTerm var])
        Untyped _ -> Right $ Name_term $ mkSimpleId l
    NumberLit l -> Left (mkEqual (mkSimpleId $ show l) $ voiToTok var,
                    mkTermAtoms (mkSimpleId $ numberName l) [mkVTerm var])

mapLit :: Int -> Literal -> Result (Either (SENTENCE, SENTENCE) TERM)
mapLit i = mapLitAux (OVar i) 

-- | Mapping of data properties
mapDataProp :: Sign -> DataPropertyExpression -> VarOrIndi -> VarOrIndi
            -> Result SENTENCE
mapDataProp _ dp a b = fmap (`mkTermAtoms` map mkVTerm [a, b])
    $ uriToTokM dp

mapDataPropI :: Sign -> VarOrIndi -> VarOrIndi -> DataPropertyExpression
             -> Result SENTENCE
mapDataPropI cSig a b dp = mapDataProp cSig dp a b

-- | Mapping of obj props
mapObjProp :: Sign -> ObjectPropertyExpression -> VarOrIndi -> VarOrIndi
            -> Result SENTENCE
mapObjProp cSig ob v1 v2 = case ob of
    ObjectProp u -> fmap (`mkTermAtoms` map mkVTerm [v1, v2]) $ uriToTokM u
    ObjectInverseOf u -> mapObjProp cSig u v2 v1

mapDPE :: Sign -> DataPropertyExpression -> Int -> Int -> Result SENTENCE
mapDPE cSig dpe x y = mapDataProp cSig dpe (OVar x) $ OVar y

mapOPE :: Sign -> ObjectPropertyExpression -> Int -> Int -> Result SENTENCE
mapOPE cSig ope x y = mapObjProp cSig ope (OVar x) $ OVar y

mapOPEList :: Sign -> Int -> Int -> [ObjectPropertyExpression]
    -> Result [SENTENCE]
mapOPEList s a b = mapM ((\ sig x1 x2 op -> mapOPE sig op x1 x2 ) s a b)

mapDPEList :: Sign -> Int -> Int -> [DataPropertyExpression]
    -> Result [SENTENCE]
mapDPEList s a b = mapM ((\ sig x1 x2 dp -> mapDPE sig dp x1 x2 ) s a b)

mapObjPropListP :: Sign -> Int -> Int
    -> [(ObjectPropertyExpression, ObjectPropertyExpression)]
    -> Result [(SENTENCE, SENTENCE)]
mapObjPropListP = mapObjOrDataListP mapOPEList

mapDataPropListP :: Sign -> Int -> Int
    -> [(DataPropertyExpression, DataPropertyExpression)]
    -> Result [(SENTENCE, SENTENCE)]
mapDataPropListP = mapObjOrDataListP mapDPEList

mapObjOrDataListP :: Monad m => (t -> t1 -> t2 -> [a] -> m [b]) -> t -> t1 -> t2
    -> [(a, a)] -> m [(b, b)]
mapObjOrDataListP f cSig a b ls = do
    let (l, r) = unzip ls
    l1 <- f cSig a b l
    l2 <- f cSig a b r
    return $ zip l1 l2

mapDataRange :: Sign -> DataRange -> VarOrIndi -> Result (SENTENCE, Sign)
mapDataRange cSig dr var = mapDataRangeAux cSig dr var (varToInt var + 1)


-- | mapping of Data Range
mapDataRangeAux :: Sign -> DataRange -> VarOrIndi -> Int -> Result (SENTENCE, Sign)
mapDataRangeAux cSig dr var i = let uid = mkVTerm var in case dr of
    DataJunction jt drl -> do
        (jl, sig) <- mapAndUnzipM ((\ s v r -> mapDataRange s r v) cSig var) drl
        let un = uniteL sig
        return $ case jt of
                IntersectionOf -> (mkBC jl, un)
                UnionOf -> (mkBD jl, un)
    DataComplementOf cdr -> do
        (dc, sig) <- mapDataRange cSig cdr var
        return (mkBN dc, sig)
    DataOneOf cs -> do
        cl <- mapM (mapLitAux var) cs
        let (sens, ts) = (lefts cl, rights cl)
            sl = map (\ (s1, s2) -> mkBC [s1, s2]) sens
        tl <- mapM (\ x -> return $ mkAtoms $ Atom x [Term_seq uid]) ts
        return (mkBD $ tl ++ sl, cSig)
    DataType dt rlst -> do
        let sent = mkTermAtoms (uriToTok dt) [uid]
        (sens, sigL) <- mapAndUnzipM (mapFacet cSig i uid) rlst
        return (mkBC $ sent : sens, uniteL $ cSig : sigL)

-- | mapping of a tuple of ConstrainingFacet and RestictionValue
mapFacet :: Sign -> Int -> TERM -> (ConstrainingFacet, RestrictionValue)
    -> Result (SENTENCE, Sign)
mapFacet sig v var (f, r) = do
    l <- mapLit v r
    let sign = unite sig $ emptySig {
                  discourseNames = Set.fromList [stringToId $ showIRI
                                                  $ stripReservedPrefix f]}
    case l of
        Right lit -> return (mkTermAtoms (uriToTok f) [lit, var], sign)
        Left (s1, s2) -> return (mkBC [mkTermAtoms (uriToTok f)
                    [mkVTerm $ OVar v, var], s1, s2], sign)

cardProps :: Bool -> Sign
    -> Either ObjectPropertyExpression DataPropertyExpression -> Int
    -> [VarOrIndi] -> Result [SENTENCE]
cardProps b cSig prop var vLst =
    if b then let Left ope = prop in mapM (mapObjProp cSig ope $ OVar var) vLst
     else let Right dpe = prop in mapM (mapDataProp cSig dpe $ OVar var) vLst

mapCard :: Bool -> Sign -> CardinalityType -> Int
    -> Either ObjectPropertyExpression DataPropertyExpression
    -> Maybe (Either ClassExpression DataRange) -> Int
    -> Result (SENTENCE, Sign)
mapCard b cSig ct n prop d var = do
    let vlst = map (var +) [1 .. n]
        vLst = map OVar vlst
        vlstM = vlst ++ [n + var + 1]
        vLstM = map OVar vlstM
    (dOut, sigL) <- case d of
        Nothing -> return ([], [])
        Just y ->
          if b then let Left ce = y in mapAndUnzipM
                        (uncurry $ mapDescription cSig ce) $ zip vLst vlst
           else let Right dr = y in mapAndUnzipM (mapDataRange cSig dr) vLst
    let dlst = map (\ (x, y) -> mkBN $ mkAE (mkNTERM x) $ mkNTERM y)
                        $ comPairs vlst vlst
        dlstM = map (\ (x, y) -> mkAE (mkNTERM x) $ mkNTERM y)
                        $ comPairs vlstM vlstM
        qVars = map mkNAME vlst
        qVarsM = map mkNAME vlstM
    oProps <- cardProps b cSig prop var vLst
    oPropsM <- cardProps b cSig prop var vLstM
    let minLst = mkQE qVars $ mkBC $ dlst ++ dOut ++ oProps
        maxLst = mkQE qVarsM $ mkBI (mkBC $ oPropsM ++ dOut) $ mkBD dlstM
    return $ case ct of
                MinCardinality -> (minLst, cSig)
                MaxCardinality -> (maxLst, cSig)
                ExactCardinality -> (mkBC [minLst, maxLst], uniteL sigL)

-- | mapping of OWL Descriptions
mapDescription :: Sign -> ClassExpression -> VarOrIndi -> Int
               -> Result (SENTENCE, Sign)
mapDescription cSig des oVar aVar =
  let varN = case oVar of
        OVar v -> mkNName v
        OIndi i -> uriToTok i
      var = case oVar of
        OVar v -> v
        OIndi _ -> aVar
  in case des of
    Expression cl -> do
        ne <- mapClassIRI cSig cl varN
        return (ne, cSig)
    ObjectJunction jt desL -> do
        (cel, dSig) <- mapAndUnzipM ((\ w x y z -> mapDescription w z x y)
                            cSig oVar aVar) desL
        let un = uniteL dSig
        return $ case jt of
                UnionOf -> (mkBD cel, un)
                IntersectionOf -> (mkBC cel, un)
    ObjectComplementOf descr -> do
        (ce, dSig) <- mapDescription cSig descr oVar aVar
        return (mkBN ce, dSig)
    ObjectOneOf il -> do
        nil <- mapM (mapIndivIRI cSig) il
        return (mkBD $ map (mkAE $ Name_term varN) nil, cSig)
    ObjectValuesFrom qt oprop descr -> let v = var + 1 in do
        ope <- mapOPE cSig oprop var v
        (ce, dSig) <- mapDescription cSig descr (OVar v) $ aVar + 1
        return $ case qt of
            SomeValuesFrom -> (mkQE [mkNAME v] $ mkBC [ope, ce], dSig)
            AllValuesFrom -> (mkQU [mkNAME v] $ mkBI ope ce, dSig)
    ObjectHasSelf oprop -> smap mapObjProp cSig oprop oVar oVar
    ObjectHasValue oprop indiv -> smap mapObjProp cSig oprop oVar (OIndi indiv)
    ObjectCardinality (Cardinality ct n oprop d) -> mapCard True cSig ct n
        (Left oprop) (fmap Left d) var
    DataValuesFrom qt dpe dr -> let varNN = mkNName $ var + 1 in do
        (drSent, drSig) <- mapDataRange cSig dr $ OVar $ var + 1
        senl <- mapM (mapDataPropI cSig (OVar var) $ OVar $ var + 1) dpe
        let sent = mkBC $ drSent : senl
        return $ case qt of
            AllValuesFrom -> (mkQU [Name varNN] sent, drSig)
            SomeValuesFrom -> (mkQE [Name varNN] sent, drSig)
    DataHasValue dpe c -> do
        let nvar = var + 1
        con <- mapLit nvar c
        case con of
            Right lit -> return (mkAtoms $ Atom (Name_term $ uriToTok dpe)
                    [mkTermSeq varN, Term_seq lit], cSig)
            Left (s1, s2) -> do
                sens <- mapDataProp cSig dpe oVar $ OVar nvar
                return (mkBC [sens, s1, s2], cSig)
    DataCardinality (Cardinality ct n dpe dr) -> mapCard False cSig ct n
        (Right dpe) (fmap Right dr) var

-- | Mapping of a list of descriptions
mapDescriptionList :: Sign -> Int -> [ClassExpression]
    -> Result ([SENTENCE], Sign)
mapDescriptionList cSig n lst = do
    (sens, lSig) <- mapAndUnzipM ((\ w x y z ->
                       mapDescription w z x y) cSig (OVar n) n) lst
    sig <- sigUnionL lSig
    return (sens, sig)

-- | Mapping of a list of pairs of descriptions
mapDescriptionListP :: Sign -> Int -> [(ClassExpression, ClassExpression)]
    -> Result ([(SENTENCE, SENTENCE)], Sign)
mapDescriptionListP cSig n lst = do
    let (l, r) = unzip lst
    (llst, ssSig) <- mapDescriptionList cSig n l
    (rlst, tSig) <- mapDescriptionList cSig n r
    return (zip llst rlst, unite ssSig tSig)

mapClassAssertion :: TERM -> (ClassExpression, SENTENCE) -> TEXT
mapClassAssertion ind (ce, sent) = case ce of
    Expression _ -> senToText sent
    _ -> senToText $ (mk1QU . mkBI (mkAE mk1NTERM ind)) sent

mapCharact :: Sign -> ObjectPropertyExpression -> Character -> Result TEXT
mapCharact cSig ope c = case c of
    Functional -> do
        so1 <- mapOPE cSig ope 1 2
        so2 <- mapOPE cSig ope 1 3
        return $ mkQUBI (map mkNAME [1, 2, 3]) [so1, so2]
                (mkNTERM 2) (mkNTERM 3)
    InverseFunctional -> do
        so1 <- mapOPE cSig ope 1 3
        so2 <- mapOPE cSig ope 2 3
        return $ mkQUBI (map mkNAME [1, 2, 3]) [so1, so2]
                (mkNTERM 1) (mkNTERM 2)
    Reflexive -> do
        so <- mapOPE cSig ope 1 1
        return $ senToText $ mk1QU so
    Irreflexive -> do
        so <- mapOPE cSig ope 1 1
        return $ senToText $ mk1QU $ mkBN so
    Symmetric -> do
        so1 <- mapOPE cSig ope 1 2
        so2 <- mapOPE cSig ope 2 1
        return $ senToText $ mkQU [mkNAME 1, mkNAME 2] $ mkBI so1 so2
    Asymmetric -> do
        so1 <- mapOPE cSig ope 1 2
        so2 <- mapOPE cSig ope 2 1
        return $ senToText $ mkQU [mkNAME 1, mkNAME 2] $ mkBI so1 $ mkBN so2
    Antisymmetric -> do
        so1 <- mapOPE cSig ope 1 2
        so2 <- mapOPE cSig ope 2 1
        return $ mkQUBI [mkNAME 1, mkNAME 2] [so1, so2] (mkNTERM 1) (mkNTERM 2)
    Transitive -> do
        so1 <- mapOPE cSig ope 1 2
        so2 <- mapOPE cSig ope 2 3
        so3 <- mapOPE cSig ope 1 3
        return $ senToText $ mkQU [mkNAME 1, mkNAME 2, mkNAME 3] $ mkBI
                (mkBC [so1, so2]) so3

mapKey :: Sign -> ClassExpression -> ([SENTENCE], [SENTENCE]) -> Int -> [Int]
    -> Result SENTENCE
mapKey cSig ce (pl, npl) p i = do
    (nce, _) <- mapDescription cSig ce (OVar 1) 1
    (c3, _) <- mapDescription cSig ce (OVar p) p
    let un = mkQU [mkNAME p] $ mkBI (mkBC $ c3 : npl)
                $ mkAE (mkNTERM p) $ mkNTERM 1
    return $ mk1QU $ mkBI nce $ mkQE (map mkNAME i) $ mkBC $ pl ++ [un]

mapSubObjProp :: Sign -> ObjectPropertyExpression -> ObjectPropertyExpression
    -> Int -> Result SENTENCE
mapSubObjProp cSig sp p a = let b = a + 1 in do
    l <- mapOPE cSig sp a b
    r <- mapOPE cSig p a b
    return $ mkQU (map mkNAME [a, b]) $ mkBI l r

mapSubObjPropChain :: Sign -> [ObjectPropertyExpression]
    -> ObjectPropertyExpression -> Int -> Result SENTENCE
mapSubObjPropChain cSig opl op a = let b = a + 1 in do
    let vars = [a + 2 .. a + length opl]
        vl = a : vars ++ [a + 1]
    npl <- sequence $ zipWith3 (mapOPE cSig) opl vl $ tail vl
    np <- mapOPE cSig op a b
    let lst = map mkNAME $ a : b : vars
    return $ mkQU lst $ mkBI (mkBC npl) np

mkEDPairs :: Sign -> [Int] -> Maybe Relation -> [(SENTENCE, SENTENCE)]
    -> Result ([TEXT], Sign)
mkEDPairs s il med pairs = do
    let ls = case fromMaybe (error "expected EDRelation") med of
         EDRelation Equivalent -> map (uncurry mkBB) pairs
         EDRelation Disjoint -> map (\ (x, y) -> mkBN $ mkBC [x, y]) pairs
         _ -> error "expected EDRelation"
    return ([eqFB il ls], s)

mapAxioms :: Sign -> Axiom -> Result ([TEXT], Sign)
mapAxioms cSig axiom = case axiom of
    
    Declaration _ _ -> return ([], cSig)

    ClassAxiom ax -> case ax of 
        SubClassOf _ sub sup -> do
            (domT, dSig) <- mapDescription cSig sub (OVar 1) 1
            ls <- mapM (\ cd -> mapDescription cSig cd (OVar 1) 1) [sup]
            rSig <- sigUnion cSig (unite dSig $ uniteL $ map snd ls)
            return (msen2Txt $ map (mk1QU . mkBI domT . fst) ls, rSig)

        EquivalentClasses _ cel -> do
            (decrsS, dSig) <- mapDescriptionListP cSig 1 $ comPairs cel cel
            mkEDPairs dSig [1] (Just $ EDRelation Equivalent) decrsS

        DisjointClasses _ cel -> do
            (decrsS, dSig) <- mapDescriptionListP cSig 1 $ comPairs cel cel
            mkEDPairs dSig [1] (Just $ EDRelation Disjoint) decrsS

        DisjointUnion _ clIri clsl -> do
            (decrs, dSig) <- mapDescriptionList cSig 1 clsl
            (decrsS, pSig) <- mapDescriptionListP cSig 1 $ comPairs clsl clsl
            let decrsP = unzip decrsS
            mcls <- mapClassIRI cSig clIri $ mkNName 1
            return ([senToText $ mk1QU $ mkBB mcls $ mkBC
                    [mkBD decrs, mkBN $ mkBC $ uncurry (++) decrsP]],
                    unite dSig pSig)

    ObjectPropertyAxiom opAxiom -> case opAxiom of
        SubObjectPropertyOf _ subOpExpr supOpExpr -> case subOpExpr of
            SubObjPropExpr_obj opExpr -> do
                os <- mapM (\ (o1, o2) -> mapSubObjProp cSig o1 o2 3)
                        $ mkPairs opExpr [supOpExpr]
                return (msen2Txt os, cSig)

            SubObjPropExpr_exprchain opExprs -> do
                os <- mapSubObjPropChain cSig opExprs supOpExpr 3
                return ([senToText os], cSig)

        EquivalentObjectProperties _ opExprs -> do
            pairs <- mapObjPropListP cSig 1 2 $ comPairs opExprs opExprs
            mkEDPairs cSig [1, 2] (Just $ EDRelation Equivalent) pairs

        DisjointObjectProperties _ opExprs -> do
            pairs <- mapObjPropListP cSig 1 2 $ comPairs opExprs opExprs
            mkEDPairs cSig [1, 2] (Just $ EDRelation Disjoint) pairs
        
        InverseObjectProperties _ opExpr1 opExpr2 -> do
            os1 <- mapM (\ o1 -> mapOPE cSig o1 1 2) [opExpr2]
            o2 <- mapOPE cSig opExpr1 2 1
            return (msen2Txt $ map (\ cd -> mkQU (map mkNAME [1, 2])
                $ mkBB cd o2) os1, cSig)

        ObjectPropertyDomain _ opExpr clExpr -> do
            tobjP <- mapOPE cSig opExpr 1 2
            tdsc <- mapM (\c -> mapDescription cSig c (OVar 1) 1) [clExpr]
            let vars = (1, 2)
            return (msen2Txt $ map (mkSent [mkNAME $ fst vars]
                        [mkNAME $ snd vars] tobjP . fst) tdsc,
                    uniteL $ map snd tdsc)

        ObjectPropertyRange _ opExpr clExpr -> do
            tobjP <- mapOPE cSig opExpr 1 2
            tdsc <- mapM (\c -> mapDescription cSig c (OVar 2) 2) [clExpr]
            let vars = (2, 1)
            return (msen2Txt $ map (mkSent [mkNAME $ fst vars]
                        [mkNAME $ snd vars] tobjP . fst) tdsc,
                    uniteL $ map snd tdsc)

        FunctionalObjectProperty _ opExpr -> do
            cl <- mapM (mapCharact cSig opExpr) [Functional]
            return (cl, cSig)

        InverseFunctionalObjectProperty _ opExpr -> do
            cl <- mapM (mapCharact cSig opExpr) [InverseFunctional]
            return (cl, cSig)

        ReflexiveObjectProperty _ opExpr -> do
            cl <- mapM (mapCharact cSig opExpr) [Reflexive]
            return (cl, cSig)

        IrreflexiveObjectProperty _ opExpr -> do
            cl <- mapM (mapCharact cSig opExpr) [Irreflexive]
            return (cl, cSig)

        SymmetricObjectProperty _ opExpr -> do
            cl <- mapM (mapCharact cSig opExpr) [Symmetric]
            return (cl, cSig)

        AsymmetricObjectProperty _ opExpr -> do
            cl <- mapM (mapCharact cSig opExpr) [Asymmetric]
            return (cl, cSig)

        TransitiveObjectProperty _ opExpr -> do
            cl <- mapM (mapCharact cSig opExpr) [Transitive]
            return (cl, cSig)

    DataPropertyAxiom dpAxiom -> case dpAxiom of
        SubDataPropertyOf _ subDpExpr supDpExpr -> do
            os1 <- mapM (\ o1 -> mapDPE cSig o1 1 2) [supDpExpr]
            o2 <- mapDPE cSig subDpExpr 1 2
            return (msen2Txt $ map (mkQU (map mkNAME [1, 2])
                . mkBI o2) os1, cSig)

        EquivalentDataProperties _ dpExprs -> do
            pairs <- mapDataPropListP cSig 1 2 $ comPairs dpExprs dpExprs
            mkEDPairs cSig [1, 2] (Just $ EDRelation Equivalent) pairs

        DisjointDataProperties _ dpExprs -> do
            pairs <- mapDataPropListP cSig 1 2 $ comPairs dpExprs dpExprs
            mkEDPairs cSig [1, 2] (Just $ EDRelation Disjoint) pairs

        DataPropertyDomain _ dpExpr clExpr -> do
            ls <- mapM (\c -> mapDescription cSig c (OIndi dpExpr) 1) [clExpr]
            oEx <- mapDPE cSig dpExpr 1 2
            return (msen2Txt $ map (mkSent [mk1NAME] [mkNAME 2] oEx
                    . fst) ls, uniteL $ map snd ls)

        DataPropertyRange _ dpExpr dr -> do
            oEx <- mapDPE cSig dpExpr 1 2
            ls <- mapM (\r-> mapDataRange cSig r $ OVar 2) [dr]
            return (msen2Txt $ map (mkSent [mkNAME 1] [mkNAME 2] oEx
                        . fst) ls, uniteL $ map snd ls )

        FunctionalDataProperty _ dpExpr -> do
            so1 <- mapDPE cSig dpExpr 1 2
            so2 <- mapDPE cSig dpExpr 1 3
            return ([mkQUBI (map mkNAME [1, 2, 3]) [so1, so2]
                            (mkNTERM 2) $ mkNTERM 3], cSig)

    DatatypeDefinition _ dt dr -> do
        (odes, dSig) <- mapDataRange cSig dr $ OVar 1
        let dtp = mkTermAtoms (uriToTok dt) [mkVTerm $ OVar 1]
        return ([senToText $ mk1QU $ mkBB dtp odes], dSig)

    HasKey _ ce opl dpl -> do
        let lo = length opl
            ld = length dpl
            uptoOP = [2 .. lo + 1]
            uptoDP = [lo + 2 .. lo + ld + 1]
            tl = lo + ld + 2
        (_, sig) <- mapDescription cSig ce (OVar 1) 1
        ol <- mapM (\ (n, o) -> mapOPE cSig o 1 n) $ zip uptoOP opl
        nol <- mapM (\ (n, o) -> mapOPE cSig o tl n) $ zip uptoOP opl
        dl <- mapM (\ (n, d) -> mapDPE cSig d 1 n) $ zip uptoDP dpl
        ndl <- mapM (\ (n, d) -> mapDPE cSig d tl n) $ zip uptoDP dpl
        keys <- mapKey cSig ce (ol ++ dl, nol ++ ndl) tl
            $ uptoOP ++ uptoDP
        return ([senToText keys], sig)

    Assertion assertion -> case assertion of
        SameIndividual _ inds -> do
            let (mi, rest) = case inds of
                    (iri:t) -> (Just iri, t)
                    _ -> (Nothing, inds)
            fs <- mapComIndivList cSig Same mi rest
            return (msen2Txt fs, cSig)

        DifferentIndividuals _ inds -> do
            let (mi, rest) = case inds of
                    (iri:t) -> (Just iri, t)
                    _ -> (Nothing, inds)
            fs <- mapComIndivList cSig Different mi rest
            return (msen2Txt fs, cSig)

        ClassAssertion _ ce iIri -> do
            l <- mapDescription cSig ce (OIndi iIri) 1
            inD <- mapIndivIRI cSig iIri
            let ocl = mapClassAssertion inD (ce, fst l)
            return ([ocl], snd l)

        ObjectPropertyAssertion _ op si ti -> do
            oPropH <- mapObjProp cSig op (OIndi si) (OIndi ti)
            return ([senToText $ oPropH], cSig)

        NegativeObjectPropertyAssertion _ op si ti -> do
            oPropH <- mapObjProp cSig op (OIndi si) (OIndi ti)
            return ([senToText $ mkBN $ oPropH], cSig)

        DataPropertyAssertion _ dp si tv -> do
            inS <- mapIndivIRI cSig si
            inT <- mapLit 1 tv
            nm <- uriToTokM dp
            dPropH <- case inT of
                    Right li -> return $ mkTermAtoms nm [inS, li]
                    Left (s1, s2) -> do
                        sens <- mapDataProp cSig dp (OIndi si) $ OVar 1
                        return $ mkBC [sens, s1, s2]
            return ([senToText $ dPropH], cSig)

        NegativeDataPropertyAssertion _ dp si tv -> do
            inS <- mapIndivIRI cSig si
            inT <- mapLit 1 tv
            nm <- uriToTokM dp
            dPropH <- case inT of
                    Right li -> return $ mkTermAtoms nm [inS, li]
                    Left (s1, s2) -> do
                        sens <- mapDataProp cSig dp (OIndi si) $ OVar 1
                        return $ mkBC [sens, s1, s2]
            return ([senToText $ mkBN $ dPropH], cSig)

    AnnotationAxiom _ -> return ([], cSig)

    Rule rule -> case rule of
        DLSafeRule _ b h ->
            let vars = Set.toList . Set.unions $ getVariablesFromAtom <$> (b ++ h)
                names = Name . uriToTok <$> vars
                f (sentences, sig, startVal) at = do
                    (sentences', sig', offsetValue) <- atomToSentence startVal sig at
                    return (sentences ++ sentences', sig', offsetValue)

                g startVal sig atoms = foldM f ([], sig, startVal) atoms
            in do
                (antecedentSen, sig, offsetValue) <- g 1 cSig b
                let antecedent = case antecedentSen of
                        [s] -> s
                        _ -> mkBools $ cnjct antecedentSen
                    
                (consequentSen, sig', lastVar) <- g offsetValue sig h
                let consequent =case consequentSen of
                        [s] -> s
                        _ -> mkBools $ cnjct consequentSen

                
                let impl = mkBools $ mkImpl antecedent consequent
                return $ ([senToText $ mkUnivQ (names ++ map mkNAME [1..lastVar - 1]) impl nullRange], sig')
        DGRule _ _ _ -> error "mapAxioms: DGRules are not supported yet!"
    
    DGAxiom _ _ _ _ _ -> error "mapAxioms: DGAxiom are not supported yet!"
        -- DGRule _  ->  -- ? Ask Mihai whether to implement and if so how? What do those represent? How to write them in Common Logic?
    -- DGAxiom _ c man   ->  -- ? Ask Mihai whether to implement and if so how?  What do those represent? How to write them in Common Logic?

iArgToTerm :: IndividualArg -> TERM
iArgToTerm arg = case arg of
    IVar v -> Name_term . uriToTok $ v
    IArg iri -> Name_term . uriToTok $ iri

iArgToVarOrIndi :: Int -> IndividualArg -> Result ([SENTENCE], VarOrIndi, Int)
iArgToVarOrIndi startVar arg = case arg of
    IVar var -> return ([], OIndi var, startVar)
    IArg iri -> return ([], OIndi iri, startVar)

iArgToIRI :: IndividualArg -> IRI
iArgToIRI arg = case arg of
    IVar var -> var
    IArg ind -> ind

dArgToVarOrIndi :: Int -> DataArg -> Result ([SENTENCE], VarOrIndi, Int)
dArgToVarOrIndi startVar arg = case arg of
    DVar var -> return $ ([], OIndi var, startVar)
    DArg lit -> do
        let var = OVar $ startVar
        let uid = mkVTerm var
        cl <- mapLit startVar lit
        let sen = case cl of
                Left (sen1, sen2) -> mkBC [sen1,sen2]
                Right term -> mkAtoms $ Atom term [Term_seq uid]
        return ([sen], var, startVar + 1)

-- make PROFILE=on restack
-- make PROFILE=on hets
mapClassExpression :: TERM -> (ClassExpression, SENTENCE) -> SENTENCE
mapClassExpression ind (ce, sent) = case ce of
    Expression _ -> sent
    _ -> (mk1QU . mkBI (mkAE mk1NTERM ind)) sent

atomToSentence :: Int -> Sign -> Atom -> Result ([SENTENCE], Sign, Int)
atomToSentence startVar cSig atom = case atom of
    ClassAtom clExpr iarg -> do 
        (sentences, var, offsetValue) <- iArgToVarOrIndi startVar iarg
        (l, sig) <- mapDescription cSig clExpr var 1
        return (mapClassExpression (iArgToTerm iarg) (clExpr, l) : sentences, sig, offsetValue)
        
    DataRangeAtom dataRange darg -> do
        (sentences, var, offsetValue) <- dArgToVarOrIndi startVar darg
        (s, sig) <- mapDataRangeAux cSig dataRange var offsetValue
        return (s : sentences, sig, offsetValue + 1)

    ObjectPropertyAtom opExpr iarg1 iarg2 -> do
        (sentences1, var1, offsetValue1) <- iArgToVarOrIndi startVar iarg1
        (sentences2, var2, offsetValue2) <- iArgToVarOrIndi offsetValue1 iarg2
        sen <- mapObjProp cSig opExpr var1 var2
        return (sen : sentences1 ++ sentences2 , cSig, offsetValue2)

    DataPropertyAtom dpExpr iarg darg -> do
            (sentences, var1, offsetValue) <- iArgToVarOrIndi startVar iarg
            case darg of
                DVar var2 -> do
                    sen <- mapDataProp cSig dpExpr var1 (OIndi var2)
                    return (sen : sentences, cSig, offsetValue)
                DArg lit -> do
                    inT <- mapLit startVar lit
                    nm <- uriToTokM dpExpr
                    case inT of
                            Right li -> return $ (mkTermAtoms nm [mkVTerm var1, li] : sentences, cSig, offsetValue)
                            Left (s1, s2) -> do
                                sen <- mapDataProp cSig dpExpr var1 $ OVar (offsetValue + 1)
                                return (mkBC [sen, s1, s2] : sentences, cSig, offsetValue + 2)

    BuiltInAtom iri args -> do
        (l, offsetValue) <- foldM (\(results, offsetValue) arg -> do
                result@(_, _, offsetValue') <- dArgToVarOrIndi offsetValue arg
                return (result : results, offsetValue')
            ) ([], startVar) args
        let sentences = concat $ map (\(s, _, _) -> s) l
        let vars = map (\(_, v, _) -> v) l
        let sen = mkTermAtoms (uriToTok iri) $ map mkVTerm vars
        return (sen:sentences, cSig, offsetValue)

    SameIndividualAtom iarg1 iarg2 -> do
            sens <- mapComIndivList cSig Same (Just $ iArgToIRI iarg1) [iArgToIRI iarg2]
            return (sens, cSig, startVar)
        
    DifferentIndividualsAtom iarg1 iarg2 -> do
            sens <- mapComIndivList cSig Different (Just $ iArgToIRI iarg1) [iArgToIRI iarg2]
            return (sens, cSig, startVar)
    _ -> error $ "atomToSentence: Unknown Atom '" ++ show atom ++ "'!"


-- helper function
addMrs :: TEXT -> TEXT_META
addMrs t = emptyTextMeta { getText = t }
