import System.Environment

import Control.Monad (forM_)
import Data.Maybe (fromJust)

import Common.Parsec()
import Common.GlobalAnnotations(emptyGlobalAnnos)
import Text.ParserCombinators.Parsec

import OWL2.AS
import OWL2.Sign (emptySign)
import OWL2.XML
import OWL2.XMLConversion
import OWL2.StaticAnalysis (basicOWL2Analysis)
import Text.XML.Light
import qualified Data.Set as Set

import Common.DocUtils
import Common.Result (maybeResult)
import OWL2.Pretty()
import qualified OWL2.ParseMS as MSParse
import qualified OWL2.ParseAS as ASParse

cmpAxioms :: OntologyDocument -> OntologyDocument -> Bool
cmpAxioms o1 o2 = Set.fromList (axioms . ontology $ o1) == Set.fromList(axioms . ontology $ o2)

processXML :: String -> IO ()
processXML file = do
    s <- readFile file
    let xml = head $ concatMap (filterElementsName $ isSmth "Ontology")
                $ onlyElems $ parseXML s
    let o1 = xmlBasicSpec mempty xml
    let p = xmlOntologyDoc emptySign o1
    let o2 = xmlBasicSpec mempty p
    if cmpAxioms o1 o2 then putStrLn "✅ success"
    else putStrLn $ "❌ parse-print-parse circle failed."
    
processParserPrinter :: FilePath -> CharParser () OntologyDocument -> (OntologyDocument -> OntologyDocument -> Bool) -> IO ()
processParserPrinter file parser cmp = do
    s <- readFile file
    case parse (parser >>= (\r -> eof >> return r)) file s of
        Left err -> putStrLn $ "❌ initial parsing failed: " ++ show err
        Right o1 -> let 
          (o1', _, _) = fromJust $ maybeResult $ basicOWL2Analysis (o1, emptySign, emptyGlobalAnnos)
          p = show $ pretty o1' in
            case parse (parser >>= (\r -> eof >> return r)) file p of
                Left err -> putStrLn $ "❌ parsing printed failed: " ++ show err
                Right o2 -> let (o2', _, _) = fromJust $ maybeResult $ basicOWL2Analysis (o2, emptySign, emptyGlobalAnnos) in
                    if cmp o1' o2' then  putStrLn "✅ success"
                    else
                        putStrLn $ "❌ parse-print-parse circle failed. Printed: " ++ show p

processOMN :: String -> IO ()
processOMN file = processParserPrinter file (MSParse.parseOntologyDocument mempty) cmpAxioms

processOFN :: String -> IO ()
processOFN file = processParserPrinter file (ASParse.parseOntologyDocument mempty) (==)

main :: IO ()
main = do
    args <- getArgs
    forM_ args (\path -> do
        let ext = reverse $ takeWhile (/= '.') (reverse path)
        case ext of
            "xml" -> processXML path
            "omn" -> processOMN path
            "mno" -> processOMN path
            "ofn" -> processOFN path)
