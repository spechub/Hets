{- |
Module      :  $Header$
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


import CSMOF.XMLKeywords

prueba :: Element -> String
prueba el = foldr ((++) . printChildrenModel) "" (findChildren modelK el)
printChildrenModel :: Element -> String
printChildrenModel el = foldr ((++) . show) "" (findChildren objectK el)


main :: IO ()
main = do  
    handle <- openFile "./tests/classExampleCSMOF.xmi" ReadMode  
    contents <- hGetContents handle 
    case parseXMLDoc contents of
	Nothing -> putStr "VACIO"
	Just el -> do
		    	--handle2 <- openFile "./tests/classExampleCSMOF_EXIT.xmi" WriteMode  
			--hPutStr handle2 (show el)
			--hClose handle2
			putStrLn (show (parseCSMOF el))
			--putStrLn (prueba el)
			
    
    hClose handle
