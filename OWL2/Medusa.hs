{- |
Module      :  $Header$
Description :  Convert OWL2 ontology to Medusa data structure
Copyright   :  (c) Till Mossakowski, Uni Magdeburg 2016
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  till@iws.cs.ovgu.de
Stability   :  provisional
Portability :  portable

Convert an OWL2 ontology to Medusa data structure,
see https://github.com/ConceptualBlending/monster_render_system
-}

module OWL2.Medusa where

import OWL2.Sign
import OWL2.MS

import Common.AS_Annotation
import Common.Id
import Common.IRI (IRI)
import Common.DocUtils
import Common.Result
import qualified Common.Lib.Rel as Rel

import Data.Maybe
import qualified Data.Set as Set

data Medusa = Medusa

-- | given an OWL ontology (iri and theory), compute the medusa data
medusa :: IRI -> (Sign, [Named Axiom])
                       -> Result Medusa
medusa iri (sig, nsens) = return Medusa

