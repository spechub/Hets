module Utils where

import System.IO
import Text.XML.Light
import XMINames

parse :: String -> (Element -> a) -> [Element] -> [a]
parse _ _ [] = []
parse s f (el : lis) =
	case (findAttr typeName el) == Just s of
		        True -> ((f el) : (parse s f lis))
		        False -> parse s f lis
