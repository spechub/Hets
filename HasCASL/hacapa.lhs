
$Header$
Authors: Christian Maeder
Year:    2002, 2003
   
test some parsers (and printers)

\begin{code}
module Main where

import HasCASL.ParseItem
import HasCASL.ParseTerm
import HasCASL.PrintAs
import HasCASL.PrintLe
import HasCASL.HToken
import Common.RunParsers
import HasCASL.RunStaticAna
import Common.Lib.Parsec
import Common.AnnoState
import Common.PrettyPrint
import Common.GlobalAnnotations

main :: IO ()
main = exec lineParser fileParser

parseA :: AParser a -> String -> a
parseA p s = case runParser p emptyAnnos "" s of 
	     Right a -> a
	     Left err -> error $ show err

lineParser, fileParser :: [(String, StringParser)]
lineParser = [
 ("MixIds", fromAParser uninstOpId),
 ("Kinds", fromAParser kind),
 ("Types", fromAParser parseType),
 ("Terms", fromAParser term),
 ("Typepattern", fromAParser typePattern),
 ("Pattern", fromAParser pattern),
 ("BasicItems", fromAParser basicItems),
 ("Items", fromAParser basicSpec)]

fileParser = [ ("BasicSpec", fromAParser basicSpec)
	     , ("analysis", toStringParser anaParser)
	     ]
\end{code}
