{- |
Module      :  ./Common/JSONOrXML.hs

License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Daniel Hackbarth <da_ha@uni-bremen.de>
-}
module Common.JSONOrXML where

import Common.Json
import Common.Result

import PGIP.Output.Mime

import Text.XML.Light

data JSONOrXML = JSON Json | XML Element

prettyPrint :: JSONOrXML -> String
prettyPrint (JSON json) = ppJson json
prettyPrint (XML xml) = ppElement xml

joinData :: JSONOrXML -> JSONOrXML -> Result JSONOrXML
joinData (JSON json1) (JSON json2) =
    let
        elem1 = ("elem1", json1)
        elem2 = ("elem2", json2)
    in
        return $ JSON $ JObject [elem1, elem2]
joinData (XML xml1) (XML xml2) =
    return $ XML $ Element (QName "pair" Nothing Nothing) [] [Elem xml1, Elem xml2] Nothing
joinData _ _ = fail "Cannot join JSON and XML!"

-- gibt json/xml aus mit einem tag, ob es json oder xml ist,
prettyWithTag :: JSONOrXML -> (String, JSONOrXML)
prettyWithTag (JSON json) = (jsonC, JSON json)
prettyWithTag (XML xml) = (xmlC, XML xml)
