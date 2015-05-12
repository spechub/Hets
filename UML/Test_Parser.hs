import           Common.AnnoParser
import           Common.DocUtils
import           Common.Parsec
import qualified Data.Map                      as Map
import           System.IO
import           Text.ParserCombinators.Parsec
import           Text.XML.Light
import           UML.Parser

main :: IO ()
main = do
    --handle <- openFile "UML/data/simplelibrary.xmi" ReadMode
    handle <- openFile "UML/data/statemachine_Till.xml" ReadMode
        --handle <- openFile "data/uml.xmi" ReadMode
    --handle <- openFile "data/statemachine.xmi" ReadMode
    contents <- hGetContents handle

    putStr $ case parse (basicSpecCM Map.empty) "" contents  of
            Left err -> show err
            Right cm -> show $ pretty cm
