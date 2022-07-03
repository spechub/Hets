module NeSyPatterns.Parse (basicSpec, symb, symbItems, symbMapItems) where

import Common.Keywords
import Common.AnnoState
import Common.Id
import Common.Lexer
import Common.Parsec

import qualified Common.GlobalAnnotations as GA (PrefixMap)

import NeSyPatterns.AS

import Data.Maybe (isJust, catMaybes)

import Text.ParserCombinators.Parsec

symb :: AParser st SYMB
symb = Symb_id <$> name

symbItems :: AParser st SYMB_ITEMS
symbItems = do
    items <- fst <$> symb `separatedBy` anComma
    let range = concatMapRange getRange items
    return $ Symb_items items range

symbOrMap :: AParser st SYMB_OR_MAP
symbOrMap = do
    s1 <- symb
    s2M <- optionMaybe (asKey mapsTo >> symb)
    case s2M of
        Nothing -> return $ Symb s1
        Just s2 -> return $ Symb_map s1 s2 (concatMapRange getRange [s1, s2])

symbMapItems :: AParser st SYMB_MAP_ITEMS
symbMapItems = do
    items <- fst <$> symbOrMap `separatedBy` anComma
    let range = concatMapRange getRange items
    return $ Symb_map_items items range


name :: AParser st Token
name = wrapAnnos $ pToken (alphaNum <:> many (alphaNum <|> char ':'))

ontologyTermP :: AParser st Token
ontologyTermP = name

nodeId :: AParser st Token
nodeId = brackets name

node :: AParser st Node
node = do
    otM <- optionMaybe ontologyTermP
    idM <- if isJust otM then optionMaybe nodeId else Just <$> nodeId
    let range = catRange . catMaybes $ [otM, idM]
    return $ Node otM idM range


basicItem :: AParser st BASIC_ITEM
basicItem = Path <$> fst <$> separatedBy node (asKey "->") << anSemi

basicSpec :: GA.PrefixMap -> AParser st BASIC_SPEC
basicSpec _ = Basic_spec <$> annosParser basicItem



-- -- Function for easier testing
-- test :: AParser () a -> String -> a
-- test p s = case runParser p (emptyAnnos ()) "NeSyPatterns.Parse.test" s of
--     Left e -> error $ "***Error:"  ++ show e
--     Right a -> a
