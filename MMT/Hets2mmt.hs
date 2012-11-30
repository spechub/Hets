{- |
   a.jakubauskas@jacobs-university.de
	
	A wrapper/interface for MMT
-}



module MMT.Hets2mmt
	where

--import System.Posix
--import System.Cmd
import System.Process
import System.IO


exampleFile = "/home/aivaras/Desktop/Hets/syntax.elf"
jar = "/home/aivaras/Hets-src/MMT/hets-mmt-standalone.jar"
dostuff fileName = rawSystem "java" ["-jar", jar, fileName]

--t = readProcessWithExitCode "java" ["-jar","MMT/hets-mmt-standalone.jar","/home/aivaras/Desktop/base.elf"] []

--r = createProcess (proc "ls" [])

main fileName = do 
	x <- dostuff fileName
	return Nothing
