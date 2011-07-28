{- |
Module      :  $Header$
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Contains    :  OWL2 Profiles (EL, QL and RL)

References  :  <http://www.w3.org/TR/owl2-profiles/>
-}

module OWL2.Profiles where

import OWL2.AS
import OWL2.MS

import Common.Id

import Data.Maybe
import Data.Char
import Data.List

import qualified Data.Set as Set

data Profiles = Profiles {
        el :: Bool,
        ql :: Bool,
        rl :: Bool
    } deriving (Show, Eq, Ord)

bottomProfile :: Profiles
bottomProfile = Profiles False False False

topProfile :: Profiles
topProfile = Profiles True True True

elProfile :: Profiles
elProfile = Profiles True False False

qlProfile :: Profiles
qlProfile = Profiles False True False

rlProfile :: Profiles
rlProfile = Profiles False False True

elqlProfile :: Profiles
elqlProfile = Profiles True True False

elrlProfile :: Profiles
elrlProfile = Profiles True False True

qlrlProfile :: Profiles
qlrlProfile = Profiles False True True

all3Profile :: Profiles
all3Profile = Profiles True True True

andProfileList :: [Profiles] -> Profiles
andProfileList pl = bottomProfile {
        el = all el pl,
        ql = all ql pl,
        rl = all rl pl
    }

andList :: (a -> Profiles) -> [a] -> Profiles
andList f cel = andProfileList (map f cel)

minimalCovering :: Profiles -> [Profiles] -> Profiles
minimalCovering c pl = andProfileList [c, andProfileList pl]

dataType :: Datatype -> Profiles
dataType dt = topProfile -- needs to be implemented, of course

literal :: Literal -> Profiles
literal l = topProfile -- needs to be implemented

individual :: Individual -> Profiles
individual i = if isAnonymous i then rlProfile else topProfile

objProp :: ObjectPropertyExpression -> Profiles
objProp ope = case ope of
    ObjectInverseOf _ -> qlrlProfile
    _ -> topProfile

dataRange :: DataRange -> Profiles
dataRange dr = case dr of
    DataType dt cfl ->
        if null cfl then dataType dt
         else bottomProfile
    DataJunction IntersectionOf drl -> andProfileList $ map dataRange drl
    DataOneOf ll -> bottomProfile {
                        el = (el $ andList literal ll) && length ll == 1
                    }
    _ -> bottomProfile

subClass :: ClassExpression -> Profiles
subClass cex = case cex of
    Expression c -> if isThing c then elqlProfile else topProfile
    ObjectJunction jt cel -> minimalCovering (case jt of
        IntersectionOf -> elrlProfile
        UnionOf -> rlProfile) $ map subClass cel
    ObjectOneOf il -> bottomProfile {
                    el = (el $ andList individual il) && length il == 1,
                    rl = ql $ andList individual il
                }
    ObjectValuesFrom SomeValuesFrom ope ce -> andProfileList [objProp ope,
        case ce of
            Expression c -> if isThing c then topProfile
                             else elrlProfile
            _ -> minimalCovering elrlProfile [subClass ce]]
    ObjectHasValue ope i -> minimalCovering elrlProfile
       [objProp ope, individual i]
    ObjectHasSelf ope -> minimalCovering elProfile [objProp ope]
    DataValuesFrom SomeValuesFrom _ dr -> dataRange dr
    DataHasValue _ l -> literal l
    _ -> bottomProfile

superClass :: ClassExpression -> Profiles
superClass cex = case cex of
    Expression c -> if isThing c then elqlProfile else topProfile
    ObjectJunction IntersectionOf cel -> andList superClass cel
    ObjectComplementOf ce -> minimalCovering qlrlProfile [subClass ce]
    ObjectOneOf il -> bottomProfile {
                    el = (el $ andList individual il) && length il == 1,
                    rl = ql $ andList individual il
                }
    ObjectValuesFrom qt ope ce -> case qt of
        SomeValuesFrom -> andProfileList [objProp ope, case ce of
            Expression _ -> elqlProfile
            _ -> elProfile]
        AllValuesFrom -> andProfileList [superClass ce, rlProfile]
    ObjectHasValue ope i -> andProfileList [elrlProfile, objProp ope,
        individual i]
    ObjectHasSelf ope -> andProfileList [elProfile, objProp ope]
    ObjectCardinality (Cardinality MaxCardinality i _ mce) ->
        if elem i [0, 1] then andProfileList [rlProfile, case mce of
            Nothing -> topProfile
            Just ce -> case ce of
                Expression _ -> topProfile
                _ -> subClass ce]
         else bottomProfile
    DataValuesFrom qt _ dr -> andProfileList [dataRange dr, case qt of
        SomeValuesFrom -> elqlProfile
        AllValuesFrom -> rlProfile]
    DataHasValue _ l -> andProfileList [elrlProfile, literal l]
    DataCardinality (Cardinality MaxCardinality i _ mdr) ->
        if elem i [0, 1] then andProfileList [rlProfile, case mdr of
            Nothing -> topProfile
            Just dr -> dataRange dr]
         else bottomProfile
    _ -> bottomProfile

equivClassRL :: ClassExpression -> Bool
equivClassRL cex = case cex of
    Expression c -> (not . isThing) c
    ObjectJunction IntersectionOf cel -> all equivClassRL cel
    ObjectHasValue _ i -> rl $ individual i
    DataHasValue _ l -> rl $ literal l
    _ -> False

annotation :: Annotation -> Profiles
annotation (Annotation as _ av) = andProfileList [annotations as, case av of
    AnnValLit l -> literal l
    _ -> topProfile]

annotations :: Annotations -> Profiles
annotations ans = andProfileList $ map annotation ans

assertionQL :: ClassExpression -> Bool
assertionQL ce = case ce of
    Expression _ -> True
    _ -> False

char :: [Character] -> [Character] -> Bool
char charList ls = all (`elem` ls) charList

fact :: Fact -> Profiles
fact f = case f of
    ObjectPropertyFact pn ope i -> andProfileList [objProp ope, individual i,
        case pn of
            Positive -> topProfile
            Negative -> elrlProfile]
    DataPropertyFact pn _ l -> andProfileList [literal l,
        case pn of
            Positive -> topProfile
            Negative -> elrlProfile]

lFB :: Extended -> Maybe Relation -> ListFrameBit -> Profiles
lFB ext mr lfb = case lfb of
    AnnotationBit anl -> annotations $ concatMap fst anl
    ExpressionBit anl ->
        let ans = annotations $ concatMap fst anl
            cel = map snd anl
            r = fromMaybe (error "relation needed") mr
        in case ext of
            Misc anno -> andProfileList [ans, annotations anno,
                bottomProfile {
                    el = el $ andList subClass cel,
                    ql = ql $ andList subClass cel,
                    rl = all equivClassRL cel
                }]
            ClassEntity c -> case r of
                SubClass -> andProfileList [ans, subClass c,
                    andList superClass cel]
                _ -> andProfileList [ans, bottomProfile {
                    el = el $ andList subClass $ c : cel,
                    ql = ql $ andList subClass $ c : cel,
                    rl = all equivClassRL $ c : cel
                }]
            ObjectEntity op -> andProfileList [ans, objProp op,
                andList superClass cel]
            SimpleEntity (Entity ty ent) -> case ty of
                DataProperty -> andProfileList [ans, andList superClass cel]
                NamedIndividual -> andProfileList [ans, individual ent,
                    bottomProfile {
                        el = el $ andList superClass cel,
                        ql = all assertionQL cel,
                        rl = rl $ andList superClass cel
                    }]
                _ -> error "invalid expression bit"
    ObjectBit anl ->
        let ans = annotations $ concatMap fst anl
            opl = andList objProp $ map snd anl
            r = fromMaybe (error "relation needed") mr
        in case ext of
            Misc anno -> andProfileList [ans, annotations anno, opl, case r of
                EDRelation Equivalent -> topProfile
                _ -> qlrlProfile]
            ObjectEntity op -> andProfileList [ans, opl, objProp op, case r of
                SubPropertyOf -> topProfile
                EDRelation Equivalent -> topProfile
                _ -> qlrlProfile]
            _ -> error "invalit object bit"
    DataBit anl ->
        let ans = annotations $ concatMap fst anl
            r = fromMaybe (error "relation needed") mr
        in case ext of
            Misc anno -> andProfileList [ans, annotations anno, case r of
                EDRelation Equivalent -> topProfile
                _ -> qlrlProfile]
            _ -> andProfileList [ans, case r of
                    SubPropertyOf -> topProfile
                    EDRelation Equivalent -> topProfile
                    _ -> qlrlProfile]
    IndividualSameOrDifferent anl ->
        let ans = annotations $ concatMap fst anl
            r = fromMaybe (error "relation needed") mr
            i = andList individual $ map snd anl
        in case ext of
            Misc anno -> andProfileList [ans, annotations anno, i, case r of
                SDRelation Different -> topProfile
                _ -> elrlProfile]
            SimpleEntity (Entity _ ind) -> andProfileList [ans, individual ind,
                i, case r of
                    SDRelation Different -> topProfile
                    _ -> elrlProfile]
            _ -> error "bad individual bit"
    ObjectCharacteristics anl ->
        let ans = annotations $ concatMap fst anl
            cl = map snd anl
        in case ext of
            ObjectEntity op -> andProfileList [ans, objProp op,
                    bottomProfile {
                        el = char cl [Reflexive, Transitive],
                        ql = char cl [Reflexive, Symmetric, Asymmetric],
                        rl = char cl [Functional, InverseFunctional,
                                Irreflexive, Symmetric, Asymmetric, Transitive]
                    }]
            _ -> error "object entity needed"
    DataPropRange anl ->
        let ans = annotations $ concatMap fst anl
            dr = andList dataRange $ map snd anl
        in andProfileList [ans, dr]
    IndividualFacts anl ->
        let ans = annotations $ concatMap fst anl
            facts = andList fact $ map snd anl
        in case ext of
            SimpleEntity (Entity _ i) ->
                andProfileList [ans, facts, individual i]
            _ -> error "bad fact bit"

aFB :: Extended -> Annotations -> AnnFrameBit -> Profiles
aFB ext anno afb =
    let ans = annotations anno
    in case afb of
        AnnotationFrameBit -> ans
        DataFunctional -> andProfileList [ans, elrlProfile]
        DatatypeBit dr -> case ext of
            SimpleEntity (Entity _ dt) -> andProfileList
                [ans, dataType dt, dataRange dr]
            _ -> error "bad datatype bit"
        ClassDisjointUnion _ -> bottomProfile
        ClassHasKey opl _ -> case ext of
            ClassEntity ce -> minimalCovering elrlProfile
                [ans, andList objProp opl, subClass ce]
            _ -> error "bad has key"
        ObjectSubPropertyChain opl -> case ext of
            ObjectEntity op -> minimalCovering elrlProfile
                [ans, andList objProp $ op : opl]
            _ -> error "bad sub property chain"

fB :: Extended -> FrameBit -> Profiles
fB ext fb = case fb of
    ListFrameBit mr lfb -> lFB ext mr lfb
    AnnFrameBit anno afb -> aFB ext anno afb

axiom :: Axiom -> Profiles
axiom (PlainAxiom ext fb) = fB ext fb

frame :: Frame -> Profiles
frame (Frame ext fbl) = andList (fB ext) fbl

ontologyP :: Ontology -> Profiles
ontologyP ont =
    let anns = ann ont
        fr = ontFrames ont
    in andProfileList [andList frame fr, andList annotations anns]

ontologyDoc :: OntologyDocument -> Profiles
ontologyDoc odoc = ontologyP $ ontology odoc

---------------------------------------------

data NumberRestrictions = None | Unqualified | Qualified
                        deriving (Show, Eq, Ord)

data OWLDatatypes = OWLDATA | OWLString |
                    OWLnormalizedString |
                    OWLBoolean | OWLDecimal | OWLFloat | OWLDouble |
                    OWLInteger | OWLnonNegativeInteger | OWLpositiveInteger |
                    OWLnonPositiveInteger | OWLnegativeInteger
               deriving (Show, Eq, Ord, Enum, Bounded)

owlDatatypes :: [OWLDatatypes]
owlDatatypes = [minBound .. maxBound]

printXSDName :: Show a => a -> String
printXSDName dt =
    drop 3 $ show dt

data OWLSub = OWLSub
            {
              numberRestrictions :: NumberRestrictions
            , nominals :: Bool
            , inverseRoles :: Bool
            , roleTransitivity :: Bool
            , roleHierarchy :: Bool
            , complexRoleInclusions :: Bool
            , addFeatures :: Bool
            , datatype :: Set.Set OWLDatatypes
            } deriving (Show, Eq, Ord)

-- | sROIQ(D)
sl_top :: OWLSub
sl_top = OWLSub
      {
        numberRestrictions = Qualified
      , nominals = True
      , inverseRoles = True
      , roleTransitivity = True
      , roleHierarchy = True
      , complexRoleInclusions = True
      , addFeatures = True
      , datatype = Set.fromList owlDatatypes
      }

-- ALC
sl_bottom :: OWLSub
sl_bottom = OWLSub
            {
              numberRestrictions = None
            , nominals = False
            , inverseRoles = False
            , roleTransitivity = False
            , roleHierarchy = False
            , complexRoleInclusions = False
            , addFeatures = False
            , datatype = Set.empty
            }


sl_max :: OWLSub -> OWLSub -> OWLSub
sl_max sl1 sl2 =
    OWLSub
    {
      numberRestrictions = max (numberRestrictions sl1)
                           (numberRestrictions sl2)
    , nominals = max (nominals sl1)
                 (nominals sl2)
    , inverseRoles = max (inverseRoles sl1)
                     (inverseRoles sl2)
    , roleTransitivity = max (roleTransitivity sl1)
                         (roleTransitivity sl2)
    , roleHierarchy = max (roleHierarchy sl1)
                      (roleHierarchy sl2)
    , complexRoleInclusions = max (complexRoleInclusions sl1)
                              (complexRoleInclusions sl2)
    , addFeatures = max (addFeatures sl1)
                    (addFeatures sl2)
    , datatype = Set.union (datatype sl1)
                 (datatype sl2)
    }

-- | Naming for Description Logics
sl_name :: OWLSub -> String
sl_name sl =
    (if complexRoleInclusions sl || addFeatures sl
       then (if addFeatures sl then "s" else "") ++ "R"
       else (if roleTransitivity sl then "S" else "ALC")
            ++ if roleHierarchy sl then "H" else "")
    ++ (if nominals sl then "O" else "")
    ++ (if inverseRoles sl then "I" else "")
    ++ (case numberRestrictions sl of
        Qualified -> "Q"
        Unqualified -> "N"
        None -> "")
    ++ let ds = datatype sl in if Set.null ds then "" else
           "(D"
           ++ (let ts = Set.filter (/= OWLDATA) ds
               in if Set.null ts then "" else
                 " {"
                 ++ (if ds == Set.fromList owlDatatypes then "..." else
                         intercalate " " $ map printXSDName $ Set.toList ts)
                 ++ "}")
           ++ ")"

requireQualNumberRestrictions :: OWLSub -> OWLSub
requireQualNumberRestrictions sl = sl { numberRestrictions = Qualified }

requireNumberRestrictions :: OWLSub -> OWLSub
requireNumberRestrictions sl =
    if numberRestrictions sl /= Qualified
       then sl {numberRestrictions = Unqualified}
       else
           sl

requireRoleTransitivity :: OWLSub -> OWLSub
requireRoleTransitivity sl = sl {roleTransitivity = True}

requireRoleHierarchy :: OWLSub -> OWLSub
requireRoleHierarchy sl = sl { roleHierarchy = True}

requireComplexRoleInclusions :: OWLSub -> OWLSub
requireComplexRoleInclusions sl =
    (requireRoleHierarchy $ requireRoleTransitivity sl)
        { complexRoleInclusions = True}

requireAddFeatures :: OWLSub -> OWLSub
requireAddFeatures sl =
    (requireComplexRoleInclusions sl)
        { addFeatures = True}

requireNominals :: OWLSub -> OWLSub
requireNominals sl = sl {nominals = True}

requireInverseRoles :: OWLSub -> OWLSub
requireInverseRoles sl = sl {inverseRoles = True}

requireDatatype :: OWLSub -> OWLSub
requireDatatype sl = sl {datatype = Set.union (datatype sl)
                             $ Set.singleton OWLDATA}

sl_obj_prop :: ObjectPropertyExpression -> OWLSub
sl_obj_prop o = case o of
      ObjectProp _ -> sl_bottom
      ObjectInverseOf p -> requireInverseRoles $ sl_obj_prop p

sl_ent :: Entity  -> OWLSub
sl_ent (Entity et _) =
    case et of
      Datatype -> requireDatatype sl_bottom
      _ -> sl_bottom

sl_data_uri :: QName -> OWLSub
sl_data_uri ur = sl_bottom
  { datatype = case namePrefix ur of
      "xsd" -> let
          l = map toLower $ localPart ur
          s = case l of
                '#' : r -> r
                _ -> l
          in Set.fromList $ OWLDATA
               : filter ((s ==) . map toLower . printXSDName) owlDatatypes
      _ -> Set.singleton OWLDATA }

sl_data_prop :: DataPropertyExpression -> OWLSub
sl_data_prop = sl_data_uri

sl_data_range :: DataRange -> OWLSub
sl_data_range rn =
    requireDatatype $
    case rn of
      DataType ur _ -> sl_data_uri ur
      DataComplementOf c -> sl_data_range c
      DataOneOf _ -> requireNominals sl_bottom
      DataJunction _ drl -> foldl sl_max sl_bottom $ map sl_data_range drl

sl_desc :: ClassExpression -> OWLSub
sl_desc des =
    case des of
      Expression _ -> sl_bottom
      ObjectJunction _ dec -> foldl sl_max sl_bottom $ map sl_desc dec
      ObjectComplementOf dec -> sl_desc dec
      ObjectOneOf _ -> requireNominals sl_bottom
      ObjectValuesFrom _ o d -> sl_max (sl_obj_prop o) (sl_desc d)
      ObjectHasSelf o -> requireAddFeatures $ sl_obj_prop o
      ObjectHasValue o _ -> sl_obj_prop o
      ObjectCardinality c -> sl_card c
      DataValuesFrom _ d dr -> requireDatatype $
             sl_max (sl_data_range dr) (sl_data_prop d)
      DataHasValue d _ -> requireDatatype $ sl_data_prop d
      DataCardinality c -> requireDatatype $ sl_d_card c

sl_d_card :: Cardinality DataPropertyExpression DataRange -> OWLSub
sl_d_card (Cardinality _ _ dp x) =
    case x of
      Nothing -> requireDatatype $
                 requireNumberRestrictions $
                 sl_data_prop dp
      Just y -> requireDatatype $
                 requireQualNumberRestrictions $
                 sl_max (sl_data_prop dp) (sl_data_range y)

sl_card :: Cardinality ObjectPropertyExpression ClassExpression
          -> OWLSub
sl_card (Cardinality _ _ op x) =
    case x of
      Nothing -> requireNumberRestrictions $
                 sl_obj_prop op
      Just y -> requireQualNumberRestrictions $
                 sl_max (sl_obj_prop op) (sl_desc y)

slLFB :: Maybe Relation -> ListFrameBit -> OWLSub
slLFB mr lfb = case lfb of
    ExpressionBit anl -> foldl sl_max sl_bottom $ map (sl_desc . snd) anl
    ObjectBit anl -> sl_max (case fromMaybe (error "relation needed") mr of
        EDRelation Disjoint -> requireAddFeatures sl_bottom
        _ -> sl_bottom) $ foldl sl_max sl_bottom $ map (sl_obj_prop . snd) anl
    DataBit anl -> sl_max (case fromMaybe (error "relation needed") mr of
        EDRelation Disjoint -> requireAddFeatures sl_bottom
        _ -> sl_bottom) $ foldl sl_max sl_bottom $ map (sl_data_prop . snd) anl
    IndividualSameOrDifferent _ -> requireNominals sl_bottom
    ObjectCharacteristics anl -> foldl sl_max sl_bottom
        $ map (\ c -> case c of 
              Transitive -> requireRoleTransitivity sl_bottom
              Reflexive -> requireAddFeatures sl_bottom
              Irreflexive -> requireAddFeatures sl_bottom
              Asymmetric -> requireAddFeatures sl_bottom
              _ -> sl_bottom) $ map snd anl
    DataPropRange anl -> foldl sl_max sl_bottom
        $ map (sl_data_range . snd) anl
    _ -> sl_bottom

slAFB :: AnnFrameBit -> OWLSub
slAFB afb = case afb of
    DatatypeBit dr -> sl_data_range dr
    ClassDisjointUnion cel -> foldl sl_max sl_bottom $ map sl_desc cel
    ClassHasKey opl dpl -> sl_max (foldl sl_max sl_bottom
            $ map sl_obj_prop opl)
            (foldl sl_max sl_bottom $ map sl_data_prop dpl)
    ObjectSubPropertyChain opl -> requireComplexRoleInclusions
        $ requireRoleHierarchy $ foldl sl_max sl_bottom $ map sl_obj_prop opl

slFB :: FrameBit -> OWLSub
slFB fb = case fb of
    AnnFrameBit _ afb -> slAFB afb
    ListFrameBit mr lfb -> sl_max (slLFB mr lfb) (case mr of
        Nothing -> slFB fb
        Just r -> case r of
            SubPropertyOf -> requireRoleHierarchy sl_bottom
            InverseOf -> requireInverseRoles sl_bottom
            _ -> sl_bottom) -- maybe addFeatures ??


    
    
        




