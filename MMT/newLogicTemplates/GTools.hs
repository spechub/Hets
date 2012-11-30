module Generic.Tools where

import System.Process
import System.IO

<insert>


jar = "/home/aivaras/Hets-src/MMT/hets-mmt-standalone.jar"

parseSpec :: String -> Maybe(ParseTree)
parseSpec fname = do 
			tree <- rawSystem "java" ["-jar", jar, fname]
		return Nothing -- should return Just(tree) on success, error on failure?

--  1. call mmt on the text
--  2. transform mmt output into ParseTree
