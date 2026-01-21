import           Common.AnnoParser
import           Common.DocUtils
import           Common.Parsec
import qualified Data.Map                      as Map
import           System.IO
import           Text.ParserCombinators.Parsec
import           Text.XML.Light
import           UML.Parser
import           UML.PrettyUML
import           UML.UML
import System.Environment (getArgs)
import UML.UML2CL
main :: IO ()
main = do
    args <- getArgs
    --handle <- openFile "UML/data/simplelibrary.xmi" ReadMode
    handle <- openFile (args!!0) ReadMode
        --handle <- openFile "data/uml.xmi" ReadMode
    --handle <- openFile "data/statemachine.xmi" ReadMode
    contents <- hGetContents handle

    putStr $ case parse (basicSpecCM Map.empty) "" contents  of
            Left err -> show err
            Right cm ->     (show $ pretty cm) ++ "\n ____ DONE ____ \n" {-++
                            (show $ retrieveSen cm)-}
