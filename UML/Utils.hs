module UML.Utils where

import System.IO
import Text.XML.Light
import UML.XMINames

parse :: String -> (Element -> a) -> [Element] -> [a]
parse _ _ [] = []
parse s f (el : lis) =
	case (findAttr typeName el) == Just s of
		        True -> ((f el) : (parse s f lis))
		        False -> parse s f lis

getStringNotInList :: String -> [String] -> String
getStringNotInList s l =  s ++ show (head [i| i <- [0..], not (elem (s ++ (show i)) l)])
