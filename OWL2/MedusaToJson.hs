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


import OWL2.Medusa
import Common.Json

-- render Medusa data as JSON string
medusaToJsonString :: Medusa -> String
medusaToJsonString = ppJson . medusaToJson

-- render Medusa data as JSON
medusaToJson :: Medusa -> Json
medusaToJson m = JObject [("Definitions",defs),("Relations",rels)]
  where defs = JArray []
        rels = JArray []


