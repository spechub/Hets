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
import OWL2.MS
import OWL2.ShipSyntax

frame2Boxes :: Axiom -> [Box]
frame2Boxes (PlainAxiom e b) = case b of
  ListFrameBit mr lfb -> listFrame2Boxes e mr lfb
  AnnFrameBit _ fb -> annFrame2Boxes e fb

annFrame2Boxes :: Extended -> AnnFrameBit -> [Box]
annFrame2Boxes e fb = case fb of
   ClassDisjointUnion cs@(_ : _) -> case e of
     ClassEntity ce -> case ce of
       Expression c -> [ConceptDecl (localPart c)
         $ Just (Eq, foldr1 DisjointC $ map ce2concept cs)]
       _ -> []
     _ -> []
   _ -> []

ce2concept :: ClassExpression -> Concept
ce2concept ce = topC

listFrame2Boxes :: Extended -> Maybe Relation -> ListFrameBit -> [Box]
listFrame2Boxes e mr lfb = []
