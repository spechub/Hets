
{- HetCATS/CASL/RunParsers.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   test some parsers (and printers)
-}

module RunParsers (exec, HetParser(HetParser)) where 

import Lexer((<<))
import Parsec
import ParsecPos
import PrettyPrint
import Pretty
import System
import RunMixfixParser (stdAnnos)

data HetParser = forall a. PrettyPrint a => HetParser (Parser a)

exec :: [(String, HetParser)] -> [(String, HetParser)] -> IO ()
exec lps fps = do l <- getArgs
		  if length l == 1 then case snd $ head $ fps of
					HetParser p -> parseSpec (head l) p
		     else if length l == 2 then
		         let opt = head l
			     file = head (tail l)
                             lps' = filter (\(s, _) -> s == opt) lps
                             fps' = filter (\(s, _) -> s == opt) fps
		         in if null lps' && null fps' then
			    putStrLn ("unknown option: " ++ opt) 
			    else if null lps' then 
				 case snd $ head $ fps' of 
					  HetParser p -> parseSpec file p 
				 else case snd $ head $ lps' of
				      HetParser p -> checkLines p file
			 else do p <- getProgName
                                 putStrLn("Usage: "++p++" [OPTIONS] <file>")
                                 putStrLn"where OPTIONS is one of:"
                                 putStrLn $ unwords
					      (map fst lps ++ map fst fps) 

checkLines :: (PrettyPrint a) => Parser a -> FilePath -> IO ()
checkLines p fileName = do s <- readFile fileName
			   putStr (unlines (scanLines p (lines s) 1))

scanLines :: (Show tok, PrettyPrint a) =>
             GenParser tok () a -> [[tok]] -> Line -> [String]
scanLines _ [] _ = []
scanLines p (x:l) n = (parseLine p x n) : (scanLines p l (n+1))

parseLine :: (Show tok, PrettyPrint a) =>
             GenParser tok () a -> [tok] -> Line -> String
parseLine p line n = let pos = setSourceLine (initialPos "") n
			 parser = do setPosition pos
				     i <- p
				     eof
				     return i
		       in result (parse parser "" line)

parseSpec :: (PrettyPrint a) => SourceName -> Parser a -> IO ()
parseSpec fileName p  =  do r <- parseFromFile (p << eof) fileName
			    putStrLn (result r)

instance (Show a, PrettyPrint b) => PrettyPrint (Either a b) where
    printText0 g r = case r of
                     Left err -> ptext ("parse error at " ++ show err ++ "\n")
		     Right x  -> printText0 g x
 
result :: (Show a, PrettyPrint b) => Either a b -> String
result r = renderText Nothing (printText0 stdAnnos r) 

