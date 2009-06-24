{- |
Module      : $Header$
Description : XML processing for the CMDL interface
Copyright   : uni-bremen and DFKI
License     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

PGIP.MarkPgip contains commands for adding pgip markup into unstructured
Hets file
-}

module PGIP.MarkPgip
where

import Text.XML.Light
import Common.Utils(trim)

genQName :: String -> QName
genQName str =
   let qnameVal = blank_name
   in qnameVal { qName = str }

genProofStep :: String -> Content
genProofStep str =
  case trim str of 
   [] -> Elem $ Element {
                 elName = genQName "whitespace",
                 elAttribs = [],
                 elContent = [Text $ CData CDataRaw str Nothing],
                 elLine = Nothing }
   '#':_ -> Elem $ Element {
                  elName = genQName "comment",
                  elAttribs = [],
                  elContent = [Text $ CData CDataRaw str Nothing],
                  elLine = Nothing }
   _ ->  Elem $ Element {
           elName = genQName "proofstep",
           elAttribs = [],
           elContent = [Text $ CData CDataRaw str Nothing],
           elLine = Nothing }

-- | adds structure to unstructured code 
addPgipMarkUp :: String -> Content
addPgipMarkUp str 
 = 
    let contents = map genProofStep $ lines str
        parseResult = Elem $ Element { 
                              elName = genQName "parseresult",
                              elAttribs = [],
                              elContent =  contents, 
                              elLine = Nothing }
    in parseResult

{- 
 - other types of mark ups : 
 -   opengoal / closegoal
 -   openblock / closeblock
 -
 -}
