module Main where

import ParseItem
import ParseTerm
import PrintAs
import HToken
import RunParsers

main :: IO ()
main = exec lineParser fileParser

lineParser, fileParser :: [(String, HetParser)]
lineParser = [
 ("id", HetParser uninstOpName),
 ("typename", HetParser typeName),
 ("type", HetParser parseType),
 ("term", HetParser term),
 ("typepattern", HetParser typePattern),
 ("pattern", HetParser pattern),
 ("item", HetParser basicSpec)]

fileParser = [("items", HetParser basicSpec)]
