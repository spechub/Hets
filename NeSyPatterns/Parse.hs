module NeSyPatterns.Parse (basicSpec, symb, symbItems, symbMapItems) where

import Common.Keywords
import Common.AnnoState
import Common.Id
import Common.IRI
import Common.Lexer
import Common.Parsec

import qualified Common.GlobalAnnotations as GA (PrefixMap)

import NeSyPatterns.AS

import Data.Maybe (isJust, catMaybes)

import Text.ParserCombinators.Parsec

symb :: GA.PrefixMap -> AParser st SYMB
symb = fmap Symb_id . node

symbItems :: GA.PrefixMap -> AParser st SYMB_ITEMS
symbItems pm = do
    is <- fst <$> symb pm `separatedBy` anComma
    let range = concatMapRange getRange is
    return $ Symb_items is range

symbOrMap :: GA.PrefixMap -> AParser st SYMB_OR_MAP
symbOrMap pm = do
    s1 <- symb pm
    s2M <- optionMaybe (asKey mapsTo >> symb pm)
    case s2M of
        Nothing -> return $ Symb s1
        Just s2 -> return $ Symb_map s1 s2 (concatMapRange getRange [s1, s2])

symbMapItems :: GA.PrefixMap -> AParser st SYMB_MAP_ITEMS
symbMapItems pm = do
    is <- fst <$> symbOrMap pm `separatedBy` anComma
    let range = concatMapRange getRange is
    return $ Symb_map_items is range

nesyKeywords :: [String]
nesyKeywords = [endS]

uriQ :: CharParser st IRI
uriQ = iriCurie

expUriP :: GA.PrefixMap -> CharParser st IRI
expUriP pm = uriP >>= return . expandIRI pm

uriP :: CharParser st IRI
uriP = try $ do
  startsWithColon <- isJust <$> (optionMaybe . try . lookAhead $ char ':')
  checkWithUsing (\i -> "keyword \"" ++ showIRI i ++ "\"") uriQ $ \ q -> let p = prefixName q in
    (not (isAbbrev q) || startsWithColon) || (not (null p) || iFragment q `notElem` nesyKeywords)

name :: GA.PrefixMap -> AParser st IRI
name pm = wrapAnnos $ expUriP pm

node :: GA.PrefixMap -> AParser st Node
node pm = do
    n <- name pm
    classM <- optionMaybe (asKey ":" >> name pm)
    let range = getRange . catMaybes $ [Just n, classM]
    return $ case classM of
        Nothing -> Node n Nothing range
        Just ot -> Node ot (Just n) range


basicItem :: GA.PrefixMap -> AParser st BASIC_ITEM
basicItem pm = Path <$> fst <$> separatedBy (node pm) (asKey "->") << anSemi

basicSpec :: GA.PrefixMap -> AParser st BASIC_SPEC
basicSpec pm = Basic_spec <$> annosParser (basicItem pm)



-- -- Function for easier testing
-- test :: AParser () a -> String -> a
-- test p s = case runParser p (emptyAnnos ()) "NeSyPatterns.Parse.test" s of
--     Left e -> error $ "***Error:"  ++ show e
--     Right a -> a
