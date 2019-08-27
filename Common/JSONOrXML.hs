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

union :: JSONOrXML -> JSONOrXML -> JSONOrXML
union (JSON json1) (JSON json2) = undefined
union (XML xml1) (XML xml2) = undefined
union _ _ = undefined
