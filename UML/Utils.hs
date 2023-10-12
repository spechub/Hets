module UML.Utils where

import           Text.XML.Light
import           UML.XMINames

parse :: Maybe String -> String -> (Element -> a) -> [Element] -> [a]
parse _ _ _ [] = []
parse xmiv s f (el : lis) =
    case (findAttr (typeName xmiv) el) == Just s of
                True -> ((f el) : (parse xmiv s f lis))
                False -> parse xmiv s f lis

getStringNotInList :: String -> [String] -> String
getStringNotInList s l =  s ++ show (head [i | i <- [0 ..], not (elem (s ++ (show i)) l)])
