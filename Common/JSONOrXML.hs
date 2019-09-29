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

-- return a JSONOrXML as String
prettyPrint :: JSONOrXML -> String
prettyPrint (JSON json) = ppJson json
prettyPrint (XML xml) = ppElement xml

-- join two JSON or XML data types
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

-- return a tuple with the type as string and the data as string
prettyWithTag :: JSONOrXML -> (String, String)
prettyWithTag (JSON json) = (jsonC, prettyPrint (JSON json))
prettyWithTag (XML xml) = (xmlC, prettyPrint (XML xml))
