module Main where
import Parsec
import CaslLanguage
import Anno_Parser

import AS_Annotation

testP p s =  case (parse p "" s) of
	     Left err -> do{ putStr "parse error at "
			   ; print err
			   }
	     Right x  -> print x

testPL par inp = testP (do { whiteSpace
			   ; res <- par 
			   ; eof
			   ; return res
			   } ) inp

main = testPL annotation "%%Aha\n"