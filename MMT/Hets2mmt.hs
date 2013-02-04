{- |
   a.jakubauskas@jacobs-university.de
	A wrapper/interface for MMT
-}

module MMT.Hets2mmt
    where

import System.Process
import System.IO

jar = "/hets-mmt-standalone.jar"
callMMT fileName = rawSystem "java" ["-jar", jar, fileName]

main fileName = do
    x <- callMMT fileName
    return Nothing
