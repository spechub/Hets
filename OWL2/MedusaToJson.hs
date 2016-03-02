{- |
Module      :  $Header$
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
import qualified Data.Set as Set

-- render Medusa data as JSON string
medusaToJsonString :: Medusa -> String
medusaToJsonString = ppJson . medusaToJson

-- render Medusa data as JSON
medusaToJson :: Medusa -> Json
medusaToJson m = JObject [("Definitions",defs),("Relations",rels)]
  where inds = Set.toList $ indivs m
        defs = JArray $ map indToJson inds
        rels = JArray []

-- convert an OWL2 individual with its type to JSON
indToJson :: (QName,QName) -> Json
indToJson (i,t) = 
  JObject [("Identifier",JString $ localPart i),
           ("Type",JString $ localPart t)]
