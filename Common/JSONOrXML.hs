{- |
Module      :  ./Common/JSONOrXML.hs

License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Daniel Hackbarth <da_ha@uni-bremen.de>
-}
module Common.JSONOrXML where

import Common.Json
import Text.XML.Light

data JSONOrXML = JSON Json | XML Element

prettyprint :: JSONOrXML -> String
prettyprint (JSON json) = ppJson json
prettyprint (XML xml) = ppElement xml

joinData :: JSONOrXML -> JSONOrXML -> JSONOrXML
joinData (JSON json1) (JSON json2) =
    let
        prover_results = ("prover_results", json1)
        development_graph = ("development_graph", json2)
    in
        JSON $ JObject [prover_results, development_graph]
joinData (XML xml1) (XML xml2) =
    XML $ Element "joint_data" [xml1, xml2]
joinData _ _ = undefined
