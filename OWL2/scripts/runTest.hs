import System.Environment
import System.Exit (exitFailure)

import Control.Monad (forM_)
import Data.List (uncons, stripPrefix)

import Common.Parsec()
import Common.GlobalAnnotations(emptyGlobalAnnos)
import Text.ParserCombinators.Parsec

import OWL2.AS
import OWL2.Sign (emptySign)
import OWL2.XML
import OWL2.XMLConversion
import OWL2.StaticAnalysis (basicOWL2Analysis)
import OWL2.Sublogic (slName, slODoc)
import Text.XML.Light
import qualified Data.Set as Set

import Common.DocUtils
import Common.Result (maybeResult, diags)
import OWL2.Pretty()
import qualified OWL2.ParseMS as MSParse
import qualified OWL2.ParseAS as ASParse

cmpAxioms :: OntologyDocument -> OntologyDocument -> Bool
cmpAxioms o1 o2 = Set.fromList (axioms . ontology $ o1) == Set.fromList(axioms . ontology $ o2)

processXML :: FilePath -> String -> IO OntologyDocument
processXML _ s = do
    let xml = head $ concatMap (filterElementsName $ isSmth "Ontology")
                $ onlyElems $ parseXML s
    let o1 = xmlBasicSpec mempty xml
    let p = xmlOntologyDoc emptySign o1
    let o2 = xmlBasicSpec mempty p
    if cmpAxioms o1 o2 then do
        putStrLn "\ESC[1;38;5;40m✔\ESC[0m success"
        return o2
    else do
        putStrLn $ "\ESC[1;38;5;196m✘\ESC[0m parse-print-parse circle failed."
        exitFailure
    
processParserPrinter :: FilePath -> String -> CharParser () OntologyDocument -> (OntologyDocument -> OntologyDocument -> Bool) -> IO OntologyDocument
processParserPrinter file s parser cmp = do
    case parse (parser >>= ((>>) eof . return)) file s of
        Left err -> do
            putStr $ "\ESC[1;38;5;196m✘\ESC[0m initial parsing failed: " ++ show err
            exitFailure
        Right o1 -> let r = basicOWL2Analysis (o1, emptySign, emptyGlobalAnnos) in case maybeResult r of
            Just (o1', _, _) -> let p = show $ pretty o1' in
                case parse (parser >>= ((>>) eof . return)) file p of
                    Left err -> do
                        putStrLn $ "\ESC[1;38;5;196m✘\ESC[0m parsing printed failed: " ++ show err
                        exitFailure
                    Right o2 -> let r' = basicOWL2Analysis (o2, emptySign, emptyGlobalAnnos) in case maybeResult r'  of
                        Just (o2', _, _) ->
                            if cmp o1' o2' then return o2'
                            else do
                                putStrLn $ "\ESC[1;38;5;196m✘\ESC[0m parse-print-parse circle failed. Printed:\n" ++ p
                                exitFailure
                        Nothing -> do
                                putStrLn $ "\ESC[1;38;5;196m✘\ESC[0m Static analysis failed on second parse: " ++ show (diags r') ++ "\nPrinted:\n" ++ p
                                exitFailure
            Nothing -> do
                putStrLn $ "\ESC[1;38;5;196m✘\ESC[0m static analysis failed: " ++ show (diags r)
                exitFailure

processOMN :: FilePath -> String -> IO OntologyDocument
processOMN file c = processParserPrinter file c (MSParse.parseOntologyDocument mempty) cmpAxioms

processOFN :: FilePath -> String -> IO OntologyDocument
processOFN file c = processParserPrinter file c (ASParse.parseOntologyDocument mempty) (==)

checkSublogic :: String -> OntologyDocument -> IO ()
checkSublogic content o = do
    case uncons (lines content) of
        Just (l, _) -> case stripPrefix "#SUBLOGIC=" l of
            Just sl -> let sl' = slName (slODoc o) in
                if sl' == sl then putStrLn "\ESC[1;38;5;40m✔\ESC[0m success"
                else do
                    putStrLn $ "\ESC[1;38;5;196m✘\ESC[0m Expected sublogic " ++ sl ++ " but got " ++ sl'
                    exitFailure
            Nothing -> putStrLn $ "\ESC[1;38;5;226m✔\ESC[0m no sublogic name specified"
        Nothing -> putStrLn "\ESC[1;38;5;40m✔\ESC[0m success"


main :: IO ()
main = do
    args <- getArgs
    forM_ args (\path -> do
        let ext = reverse $ takeWhile (/= '.') (reverse path)
        content <- readFile path
        o <- case ext of
            "xml" -> processXML path content
            "omn" -> processOMN path content
            "mno" -> processOMN path content
            "ofn" -> processOFN path content
            _ -> putStrLn ("Unkown extension: " ++ ext) >> exitFailure
        checkSublogic content o)
