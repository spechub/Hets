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

testFile par name = do { inp <- readFile name
		       ; sequence (map (testLine par) (lines inp))
		       }
    where testLine p line = do { putStr "** Input was: "
			       ; print line
			       ; putStr "** Result is: "
			       ; testPL p line
			       }

testData p s = parse (do {whiteSpace ; res <- p; eof ; return res}) "" s

main = testPL annotation "%%Aha\n"

testId = testPL (sepBy casl_id semi) 
	 "__++__ ; __+*[y__,a_l'__,4]__ ; {__}[__] ; __a__b[__z]" 
