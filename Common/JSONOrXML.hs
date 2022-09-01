{- |
Module      :  ./Common/JSONOrXML.hs

License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Daniel Hackbarth <da_ha@uni-bremen.de>
-}
module Common.JSONOrXML where

import Common.Json
import Common.Result
import qualified Control.Monad.Fail as Fail

import PGIP.Output.Mime

import Text.XML.Light

data JSONOrXML = JSON Json | XML Element

-- return a JSONOrXML as String
prettyPrint :: JSONOrXML -> String
prettyPrint (JSON json) = ppJson json
prettyPrint (XML xml) = ppElement xml

-- join two JSON or XML data types
joinData :: (String, JSONOrXML) -> (String, JSONOrXML) -> Result JSONOrXML
joinData (str1, (JSON json1)) (str2, (JSON json2)) =
    let
        elem1 = (str1, json1)
        elem2 = (str2, json2)
    in
        return $ JSON $ JObject [elem1, elem2]
joinData (str1, (XML xml1)) (str2, (XML xml2)) =
    let
        elem1 = Element (QName str1 Nothing Nothing) [] [Elem xml1] Nothing
        elem2 = Element (QName str2 Nothing Nothing) [] [Elem xml2] Nothing
    in
    return $ XML $ Element (QName "pair" Nothing Nothing) [] [Elem elem1, Elem elem2] Nothing
joinData _ _ = Fail.fail "Cannot join JSON and XML!"

-- return a tuple with the type as string and the data as string
prettyWithTag :: JSONOrXML -> (String, String)
prettyWithTag (JSON json) = (jsonC, prettyPrint (JSON json))
prettyWithTag (XML xml) = (xmlC, prettyPrint (XML xml))
