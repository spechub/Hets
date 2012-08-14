{- |
Module      :  $Header$
Copyright   :  (c) C. Maeder DFKI GmbH 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

convert ontology to SHIP syntax
-}

module OWL2.MS2Ship where

import OWL2.AS
import OWL2.Keywords
import OWL2.MS
import OWL2.ShipSyntax

import Data.Maybe

frame2Boxes :: Frame -> [Box]
frame2Boxes (Frame e bs) = case e of
  ClassEntity ce -> concatMap (classFrame2Boxes $ ce2Concept ce) bs
  ObjectEntity ope -> concatMap (opFrame2Boxes $ ope2Role ope) bs
  SimpleEntity (Entity et i) -> case et of
    NamedIndividual -> concatMap (indFrame2Boxes $ localPart i) bs
    _ -> []
  Misc _ -> concatMap miscFrame2Boxes bs

classFrame2Boxes :: Concept -> FrameBit -> [Box]
classFrame2Boxes c b = case b of
  ListFrameBit mr lfb -> classListFrame2Boxes c mr lfb
  AnnFrameBit _ fb -> classAnnFrame2Boxes c fb

classAnnFrame2Boxes :: Concept -> AnnFrameBit -> [Box]
classAnnFrame2Boxes c fb = case fb of
  ClassDisjointUnion cs@(_ : _) -> [ConceptDecl c
    $ Just (Eq, foldr1 DisjointC $ map ce2Concept cs)]
  _ -> []

classListFrame2Boxes :: Concept -> Maybe Relation -> ListFrameBit -> [Box]
classListFrame2Boxes c mr lfb = case lfb of
  ExpressionBit l -> let cs = map (ce2Concept . snd) l in case mr of
    Just r -> case r of
      SubClass -> map (\ d -> ConceptDecl c $ Just (Less, d)) cs
      EDRelation ed -> map ((case ed of
        Disjoint -> disC
        Equivalent -> eqC) c) cs
      _ -> []
    _ -> []
  _ -> []

opFrame2Boxes :: Role -> FrameBit -> [Box]
opFrame2Boxes r b = case b of
  ListFrameBit mr lfb -> opListFrame2Boxes r mr lfb
  AnnFrameBit {} -> []

opListFrame2Boxes :: Role -> Maybe Relation -> ListFrameBit -> [Box]
opListFrame2Boxes r mr lfb = case mr of
    Just rel -> case rel of
      DRRelation dr -> case lfb of
        ExpressionBit l -> let cs = map (ce2Concept . snd) l in case dr of
          ADomain -> map (\ c -> RoleDecl (RoleType r c topC) Nothing) cs
          ARange -> map (\ c -> RoleDecl (RoleType r topC c) Nothing) cs
        _ -> []
      _ -> case lfb of
        ObjectBit l -> let
          opes = map (ope2Role . snd) l
          rtd o t = RoleDecl (r2RT r) $ Just (o, t)
          in case rel of
          SubPropertyOf -> map (rtd Less . r2RT) opes
          InverseOf -> map (rtd Eq . r2RT . UnOp InvR) opes
          EDRelation er -> map ((case er of
            Equivalent -> eqR
            Disjoint -> disR) r) opes
          _ -> []
        _ -> []
    Nothing -> case lfb of
        ObjectCharacteristics l -> map ((`RoleKind` r) . snd) l
        _ -> []

indFrame2Boxes :: String -> FrameBit -> [Box]
indFrame2Boxes i b = case b of
  ListFrameBit mr lfb -> indListFrame2Boxes i mr lfb
  AnnFrameBit {} -> []

indListFrame2Boxes :: String -> Maybe Relation -> ListFrameBit -> [Box]
indListFrame2Boxes i mr lfb = case lfb of
    ExpressionBit l | mr == Just Types ->
      map (NominalCDecl i . ce2Concept . snd) l
    IndividualFacts l | isNothing mr ->
      concatMap (\ f -> case snd f of
        ObjectPropertyFact pn ope j ->
          [NominalRDecl i (localPart j)
          $ (if pn == Positive then id else UnOp NotR) $ ope2Role ope]
        DataPropertyFact {} -> []) l
    IndividualSameOrDifferent l -> case mr of
      Just (SDRelation sd) -> map
        ((if sd == Same then eqC else disC) (NominalC i) . i2c . snd) l
      _ -> []
    _ -> []

miscFrame2Boxes :: FrameBit -> [Box]
miscFrame2Boxes b = case b of
    ListFrameBit mr lfb -> miscListFrame2Boxes mr lfb
    AnnFrameBit {} -> []

miscListFrame2Boxes :: Maybe Relation -> ListFrameBit -> [Box]
miscListFrame2Boxes mr lfb = case mr of
  Just jr -> case jr of
    EDRelation ed -> case lfb of
      ExpressionBit l -> let cs = map (ce2Concept . snd) l in
        if ed == Disjoint then [DisjointCs cs] else mkCycle eqC cs
      ObjectBit l -> let opes = map (ope2Role . snd) l in
        if ed == Disjoint then disRs opes else mkCycle eqR opes
      _ -> []
    SDRelation sd -> case lfb of
      IndividualSameOrDifferent l -> let ics = map (i2c . snd) l in
        if sd == Same then mkCycle eqC ics else [DisjointCs ics]
      _ -> []
    _ -> []
  Nothing -> []

eqC :: Concept -> Concept -> Box
eqC c d = ConceptDecl c $ Just (Eq, d)

disC :: Concept -> Concept -> Box
disC c d = DisjointCs [c, d]

eqR :: Role -> Role -> Box
eqR r t = RoleDecl (r2RT r) $ Just (Eq, r2RT t)

mkCycle :: (a -> a -> b) -> [a] -> [b]
mkCycle f l = case l of
  h : r@(_ : t) -> (if null t then [] else [f (last t) h])
               ++ zipWith f l r
  _ -> []

disR :: Role -> Role -> Box
disR r t = RoleDecl (r2RT botR)
  $ Just (Eq, r2RT $ JoinedR IntersectionOf [r, t])

disRs :: [Role] -> [Box]
disRs rs = case rs of
  hd : tl -> map (disR hd) tl ++ disRs tl
  [] -> []

r2RT :: Role -> RoleType
r2RT r = RoleType r topC topC

i2c :: IRI -> Concept
i2c = NominalC . localPart

ce2Concept :: ClassExpression -> Concept
ce2Concept ce = case ce of
    Expression c -> let s = localPart c in
      if isThing c then if s == thingS then topC else NotC topC
      else CName s
    ObjectJunction t cs -> JoinedC t $ map ce2Concept cs
    ObjectComplementOf c -> NotC $ ce2Concept c
    ObjectOneOf is -> JoinedC UnionOf $ map i2c is
    ObjectValuesFrom q ope c -> Quant (Left q) (ope2Role ope) $ ce2Concept c
    ObjectHasValue ope i -> Quant (Left SomeValuesFrom) (ope2Role ope) $ i2c i
    -- the following translations are partly workarounds
    ObjectHasSelf ope -> Quant (Left SomeValuesFrom) (ope2Role ope)
      $ CName selfS
    ObjectCardinality (Cardinality t i ope mc) -> Quant (Right (t, i))
      (ope2Role ope) $ maybe topC ce2Concept mc
    _ -> CName dATAS

ope2Role :: ObjectPropertyExpression -> Role
ope2Role ope = case ope of
    ObjectProp o -> let r = localPart o in
      if isPredefObjProp o then if r == topObjProp then topR else botR
      else RName r
    ObjectInverseOf e -> UnOp InvR $ ope2Role e
