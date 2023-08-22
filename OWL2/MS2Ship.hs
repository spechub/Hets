{- |
Module      :  ./OWL2/MS2Ship.hs
Copyright   :  (c) C. Maeder DFKI GmbH 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

convert ontology to SHIP syntax
-}

module OWL2.MS2Ship where

import qualified OWL2.AS as AS
import Common.IRI
import OWL2.Keywords
import OWL2.MS
import OWL2.ShipSyntax

import Common.Doc
import Common.Utils

import Data.Function
import Data.Maybe
import qualified Data.Set as Set

ppShipOnt :: AS.OntologyDocument -> Doc
ppShipOnt = ppBox . catBoxes . map frame2Boxes . ontFrames . ontology

emptyBox :: Box
emptyBox = Box [] [] []

appBoxes :: Box -> Box -> Box
appBoxes (Box t1 r1 a1) (Box t2 r2 a2) = Box (t1 ++ t2) (r1 ++ r2) (a1 ++ a2)

catBoxes :: [Box] -> Box
catBoxes = foldr appBoxes emptyBox

frame2Boxes :: Frame -> Box
frame2Boxes (Frame e bs) = case e of
  ClassEntity ce -> Box (concatMap (classFrame2Boxes $ ce2Concept ce) bs) [] []
  ObjectEntity ope -> let
    r = ope2Role ope
    es = concatMap (opFrame2Boxes r) bs
    (ds, rs) = getRoleType r es
    rt = on RoleType intersectConcepts ds rs
    in Box [] (nubOrd $ map (setRoleType r rt) es) []
  SimpleEntity (AS.Entity _ et i) -> case et of
    AS.NamedIndividual -> Box [] [] $ concatMap (indFrame2Boxes $ show $ iriPath i) bs
    _ -> Box [] [] []
  Misc _ -> catBoxes $ map miscFrame2Boxes bs

classFrame2Boxes :: Concept -> FrameBit -> [TBox]
classFrame2Boxes c b = case b of
  ListFrameBit mr lfb -> classListFrame2Boxes c mr lfb
  AnnFrameBit _ fb -> classAnnFrame2Boxes c fb

classAnnFrame2Boxes :: Concept -> AnnFrameBit -> [TBox]
classAnnFrame2Boxes c fb = case fb of
  ClassDisjointUnion cs@(_ : _) -> [ConceptDecl c
    . ConceptRel Eq . JoinedC Nothing $ map ce2Concept cs]
  AnnotationFrameBit Declaration -> [ConceptDecl c $ ADTCons []]
  _ -> []

classListFrame2Boxes :: Concept -> Maybe AS.Relation -> ListFrameBit -> [TBox]
classListFrame2Boxes c mr lfb = case lfb of
  ExpressionBit l -> let cs = map (ce2Concept . snd) l in case mr of
    Just r -> case r of
      AS.SubClass -> map (ConceptDecl c . ConceptRel Less) cs
      AS.EDRelation ed -> map ((case ed of
        AS.Disjoint -> disC
        AS.Equivalent -> eqC) c) cs
      _ -> []
    _ -> []
  _ -> []

opFrame2Boxes :: Role -> FrameBit -> [RBox]
opFrame2Boxes r b = case b of
  ListFrameBit mr lfb -> opListFrame2Boxes r mr lfb
  AnnFrameBit _ fb -> case fb of
    AnnotationFrameBit Declaration -> [RoleDecl r topRT]
    _ -> []

opListFrame2Boxes :: Role -> Maybe AS.Relation -> ListFrameBit -> [RBox]
opListFrame2Boxes r mr lfb = case mr of
    Just rel -> case rel of
      AS.DRRelation dr -> case lfb of
        ExpressionBit l -> let cs = map (ce2Concept . snd) l in case dr of
          AS.ADomain -> map (\ c -> RoleDecl r (RoleType c topC)) cs
          AS.ARange -> map (RoleDecl r . RoleType topC) cs
        _ -> []
      _ -> case lfb of
        ObjectBit l -> let opes = map (ope2Role . snd) l in case rel of
          AS.SubPropertyOf -> map (RoleRel r Less) opes
          AS.InverseOf -> map (RoleRel r Eq . UnOp InvR) opes
          AS.EDRelation er -> map ((case er of
            AS.Equivalent -> eqR
            AS.Disjoint -> disR) r) opes
          _ -> []
        _ -> []
    Nothing -> case lfb of
        ObjectCharacteristics l -> map ((`RoleProp` r) . snd) l
        _ -> []

getRoleType :: Role -> [RBox] -> ([Concept], [Concept])
getRoleType r = foldr (\ b p@(ds, rs) -> case b of
  RoleDecl r2 (RoleType d e) | r == r2 -> (d : ds, e : rs)
  _ -> p) ([], [])

setRoleType :: Role -> RoleType -> RBox -> RBox
setRoleType r1 r b = case b of
  RoleDecl r2 _ | r1 == r2 -> RoleDecl r1 r
  _ -> b

flatIntersection :: Concept -> [Concept]
flatIntersection c = case c of
  JoinedC (Just AS.IntersectionOf) cs -> concatMap flatIntersection cs
  _ -> [c]

intersectConcepts :: [Concept] -> Concept
intersectConcepts = (\ l -> case l of
  [] -> topC
  [c] -> c
  _ -> JoinedC (Just AS.IntersectionOf) l)
  . Set.toList . Set.delete topC . Set.fromList . concatMap flatIntersection

indFrame2Boxes :: String -> FrameBit -> [ABox]
indFrame2Boxes i b = case b of
  ListFrameBit mr lfb -> indListFrame2Boxes i mr lfb
  AnnFrameBit {} -> []

indListFrame2Boxes :: String -> Maybe AS.Relation -> ListFrameBit -> [ABox]
indListFrame2Boxes i mr lfb = case lfb of
    ExpressionBit l | mr == Just AS.Types ->
      map (AConcept i . ce2Concept . snd) l
    IndividualFacts l | isNothing mr ->
      concatMap (\ f -> case snd f of
        ObjectPropertyFact pn ope j ->
          [ARole i (show $ iriPath j)
          $ (if pn == AS.Positive then id else UnOp NotR) $ ope2Role ope]
        DataPropertyFact {} -> []) l
    IndividualSameOrDifferent l -> case mr of
      Just (AS.SDRelation sd) -> map (AIndividual i sd . show . iriPath . snd) l
      _ -> []
    _ -> []

miscFrame2Boxes :: FrameBit -> Box
miscFrame2Boxes b = case b of
    ListFrameBit mr lfb -> miscListFrame2Boxes mr lfb
    AnnFrameBit {} -> emptyBox

miscListFrame2Boxes :: Maybe AS.Relation -> ListFrameBit -> Box
miscListFrame2Boxes mr lfb = case mr of
  Just jr -> case jr of
    AS.EDRelation ed -> case lfb of
      ExpressionBit l -> let cs = map (ce2Concept . snd) l in
        Box (if ed == AS.Disjoint then [DisjointCs cs] else mkCycle eqC cs) [] []
      ObjectBit l -> let opes = map (ope2Role . snd) l in
        Box [] (if ed == AS.Disjoint then disRs opes else mkCycle eqR opes) []
      _ -> emptyBox
    AS.SDRelation sd -> case lfb of
      IndividualSameOrDifferent l -> let is = map (iriPath . snd) l in
        Box [] [] $ (if sd == AS.Same then mkCycle else pairwise)
         (`AIndividual` sd) (map show is)
      _ -> emptyBox
    _ -> emptyBox
  Nothing -> emptyBox

eqC :: Concept -> Concept -> TBox
eqC c d = ConceptDecl c $ ConceptRel Eq d

disC :: Concept -> Concept -> TBox
disC c d = DisjointCs [c, d]

eqR :: Role -> Role -> RBox
eqR = (`RoleRel` Eq)

mkCycle :: (a -> a -> b) -> [a] -> [b]
mkCycle f l = case l of
  h : r@(_ : t) -> (if null t then [] else [f (last t) h])
               ++ zipWith f l r
  _ -> []

pairwise :: (a -> a -> b) -> [a] -> [b]
pairwise f l = case l of
  [] -> []
  h : t -> map (f h) t ++ pairwise f t

disR :: Role -> Role -> RBox
disR r t = RoleRel botR Eq $ JoinedR (Just AS.IntersectionOf) [r, t]

disRs :: [Role] -> [RBox]
disRs = pairwise disR

topRT :: RoleType
topRT = RoleType topC topC

i2c :: IRI -> Concept
i2c = NominalC . show . iriPath

ce2Concept :: AS.ClassExpression -> Concept
ce2Concept ce = case ce of
    AS.Expression c -> let s = show $ iriPath c in
      if AS.isThing c then if s == thingS then topC else NotC topC
      else CName s
    AS.ObjectJunction t cs -> JoinedC (Just t) $ map ce2Concept cs
    AS.ObjectComplementOf c -> NotC $ ce2Concept c
    AS.ObjectOneOf is -> JoinedC (Just AS.UnionOf) $ map i2c is
    AS.ObjectValuesFrom q ope c -> Quant (Left q) (ope2Role ope) $ ce2Concept c
    AS.ObjectHasValue ope i -> Quant (Left AS.SomeValuesFrom) (ope2Role ope) $ i2c i
    -- the following translations are partly workarounds
    AS.ObjectHasSelf ope -> Quant (Left AS.SomeValuesFrom) (ope2Role ope)
      $ CName selfS
    AS.ObjectCardinality (AS.Cardinality t i ope mc) -> Quant (Right (t, i))
      (ope2Role ope) $ maybe topC ce2Concept mc
    _ -> CName dATAS

ope2Role :: AS.ObjectPropertyExpression -> Role
ope2Role ope = case ope of
    AS.ObjectProp o -> let r = show $ iriPath o in
      if AS.isPredefObjProp o then if r == topObjProp then topR else botR
      else RName r
    AS.ObjectInverseOf e -> UnOp InvR $ ope2Role e
