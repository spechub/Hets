module Main where

import OmdocHXT

main::IO ()
main = do
	omdoc <- mkOmdocFromURI "examples/example.omdoc"
	putStrLn $ show omdoc
	putStrLn $ show (getTheories omdoc)

