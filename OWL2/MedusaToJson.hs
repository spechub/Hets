{- |
Module      :  ./OWL2/MedusaToJson.hs
Description :  JSON output for Medusa
Copyright   :  (c) Uni Magdeburg 2016
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  till@iws.cs.ovgu.de
Stability   :  provisional
Portability :  non-portable

JSON output for Medusa
-}

module OWL2.MedusaToJson (medusaToJson, medusaToJsonString) where

import OWL2.AS
import OWL2.Medusa
import Common.Json
import Common.IRI
import qualified Data.Set as Set

-- render Medusa data as JSON string
medusaToJsonString :: Medusa -> String
medusaToJsonString = ppJson . medusaToJson

-- render Medusa data as JSON
medusaToJson :: Medusa -> Json
medusaToJson m = JObject [("Definitions",defs),("Relations",rels)]
  where inds = Set.toList $ indivs m
        mrels = Set.toList $ relations m
        defs = JArray $ map indToJson inds
        rels = JArray $ map relToJson mrels

-- convert an OWL2 individual with its type to JSON
indToJson :: (IRI, IRI) -> Json
indToJson (i,t) =
  JObject [("Identifier",JString $ abbrevPath i),
           ("Type",JString $ abbrevPath t)]

-- convert a relation to JSON
relToJson :: (IRI, IRI, IRI, IRI) -> Json
relToJson (i1, p1, i2, p2) =
 JObject [("Individual1", JString $ abbrevPath i1),
          ("Point1", JString $ abbrevPath p1),
          ("Individual2", JString $ abbrevPath i2),
          ("Point2", JString $ abbrevPath p2)]
