module Main where

import System
import Parsec
import ParsecPerm
import CaslLanguage
import Anno_Parser

import Id

import AS_Annotation
import Token

-- import Prepositional

-- # import LogicGraph

data TtT = TtT {f_::String , pY:: Pos} deriving Show {-! derive: update !-}

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

parseFile par name = do { inp <- readFile name
			;  case (parse (parL par) name inp) of
			  Left err -> do{ putStr "parse error at "
					; print err
					}
			  Right x  -> print x
			}
    where parL p = do { whiteSpace
		      ; res <- p 
		      ; eof
		      ; return res
		      }

testFile par name = do { inp <- readFile name
		       ; sequence (map (testLine par) (lines inp))
		       }
    where testLine p line = do { putStr "** Input was: "
			       ; print line
			       ; putStr "** Result is: "
			       ; testPL p line
			       }

testFileC name = do { inp <- readFile name
		    ; sequence (map (testLine) (lines inp))
		    }
    where testLine line = do { putStr "** Input was: "
			     ; putStrLn line
			     ; putStr "** Result(KL) is: "
			     ; test_id casl_id line
			     ; putStr "** Result(CM) is: "
			     ; test_id parseId line
			       }

testData p s = parse (do {whiteSpace ; res <- p; eof ; return res}) "" s

test_id p inp = case (testData p inp) of 
		Left err -> print err
		Right id@(Id mix comp _) -> do { if comp == [] then 
					       putChar 'M' 
					       else 
					       putChar 'C'
					     ; putStr ": " 
					     ; putStrLn (showId id "") }

main = do { as <- getArgs
	  ; (p,files) <- return (extract_par as)
	  ; sequence (map (parseFile' p) files)  
	  }
    where extract_par = extract_par' "annotations" [] 
	  extract_par' p ac as = 
	      if as == [] then
		 error "*** No Filename or argument given"
	      else
	      case as of 
		      [s] -> (p,ac ++ as) 
		      x:ltl@(y:tl) -> if x == "-p" then
				      extract_par' y ac tl
				      else 
				      extract_par' p (ac++x:[]) (ltl)	 
	  parseFile' s = case s of
			 "annotations" -> parseFile annotations
			 "casl_id"     -> testFileC' 
			 otherwise     -> error ("*** unknown parser " ++ s)
	  testFileC' s = do { testFileC s
			    ; return ()
			    }
	      
testId = testPL (sepBy casl_id semi) 
	 "__++__ ; __+*[y__,a_l'__,4]__ ; {__}[__] ; __a__b[__z]" 
