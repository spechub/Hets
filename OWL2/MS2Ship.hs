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

frame2Boxes :: Frame -> [Box]
frame2Boxes (Frame e bs) = case e of
  ClassEntity ce -> concatMap (classFrame2Boxes $ ce2Concept ce) bs
  ObjectEntity ope -> concatMap (opFrame2Boxes $ ope2Role ope) bs
  SimpleEntity (Entity _ _) -> []
  Misc _ -> []

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
      EDRelation ed -> case ed of
        Disjoint -> map (\ d -> DisjointCs [c, d]) cs
        Equivalent -> map (\ d -> ConceptDecl c $ Just (Eq, d)) cs
      _ -> []
    _ -> []
  _ -> []

opFrame2Boxes :: Role -> FrameBit -> [Box]
opFrame2Boxes r b = case b of
  ListFrameBit mr lfb -> opListFrame2Boxes r mr lfb
  AnnFrameBit _ fb -> opAnnFrame2Boxes r fb

opListFrame2Boxes :: Role -> Maybe Relation -> ListFrameBit -> [Box]
opListFrame2Boxes r mr lfb = []

opAnnFrame2Boxes :: Role -> AnnFrameBit -> [Box]
opAnnFrame2Boxes r fb = []

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
      (ope2Role ope) $ maybe (CName selfS) ce2Concept mc
    _ -> CName dATAS

ope2Role :: ObjectPropertyExpression -> Role
ope2Role ope = case ope of
    ObjectProp o -> let r = localPart o in
      if isPredefObjProp o then if r == topObjProp then topR else UnOp NotR topR
      else RName r
    ObjectInverseOf e -> UnOp InvR $ ope2Role e
