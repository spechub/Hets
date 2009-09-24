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

-- Generates a QName tag named as the input string
genQName :: String -> QName
genQName str = let qnameVal = blank_name in qnameVal { qName = str }


-- Converts any line text that does not stand for a
-- comment into a theoryitem element
genProofStep :: String -> Content
genProofStep str =
  Elem Element {
    elName = genQName name,
    elAttribs = [],
    elContent = [Text $ CData CDataRaw (str++"\n") Nothing],
    elLine = Nothing
  }
  where
    name = case trim str of
             []    -> "whitespace"  -- empty line generates a whitespace element
             '#':_ -> "comment"     -- comments start with #
             _     -> "theoryitem"  -- convert line into a theoryitem element

-- | adds xml structure to unstructured code
addPgipMarkUp :: String -> Content
addPgipMarkUp str
 =
    -- split text in lines
    let allLines = lines str
        --  map all lines except the first one to theory items
        contents = map genProofStep $ tail allLines
        -- generate a opentheory element that contains
        -- the first line of code (as the trigger that causes
        -- the opentheory, it can even be a comment)
        opTheory = Elem Element {
                    elName = genQName "opentheory",
                    elAttribs = [Attr {
                                  attrKey = genQName "thyname",
                                  attrVal = "whatever"
                                      }],
                    elContent = [Text $ CData CDataRaw
                                     (if null allLines
                                      then error "empty head in addPgipMarkUp"
                                      else head allLines ++ "\n") Nothing],
                    elLine = Nothing }
        -- generate a close theory element
        clTheory = Elem Element {
                    elName = genQName "closetheory",
                    elAttribs = [],
                    elContent = [],
                    elLine = Nothing }
        -- create a suitable structure by having first the opentheory
        -- element, followed by the theoryitem elements and in the end
        -- the close theory element
        parseResult = Elem Element {
                              elName = genQName "parseresult",
                              elAttribs = [],
                              elContent = [opTheory] ++
                                          contents++[clTheory] ,
                              elLine = Nothing }
    in parseResult

{-
 - other types of mark ups :
 -   opengoal / closegoal
 -   openblock / closeblock
 -
 -}
