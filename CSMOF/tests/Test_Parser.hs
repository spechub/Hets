{- |
Module      :  ./CSMOF/tests/Test_Parser.hs
Description :  Test case for CSMOF parsing, parses a file and shows the resulting CSMOF metamodel
Copyright   :  (c) Daniel Calegari Universidad de la Republica, Uruguay 2013
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  dcalegar@fing.edu.uy
Stability   :  provisional
Portability :  portable
-}

-- From the CSMOF folder run: ghc -i.. -o main Test_Parser.hs


import CSMOF.As
import CSMOF.Parser
import CSMOF.Print

import Text.XML.Light
import System.IO

import Common.Doc
import Common.DocUtils


main :: IO ()
main = do
    handle <- openFile "RDBMSWMult_TechRep.xmi" ReadMode
    contents <- hGetContents handle
    case parseXMLDoc contents of
        Nothing -> putStr "VACIO"
        Just el ->
                        {- handle2 <- openFile "./tests/RDBMSWMult_TechRep_EXIT.xmi" WriteMode
                        hPutStr handle2 (show el)
                        hClose handle2 -}
                        print $ pretty $ parseCSMOF el
    hClose handle
