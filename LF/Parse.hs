{- |
Module      :  ./LF/Parse.hs
Description :  A parser for the Edinburgh Logical Framework
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable
-}

module LF.Parse
       ( basicSpec
       , symbItems
       , symbMapItems
       ) where

import Text.ParserCombinators.Parsec

import Common.Parsec
import Common.AnnoState
import Common.Lexer
import Common.Token
import Common.Keywords
import Common.GlobalAnnotations (PrefixMap)

import Data.Char

import LF.AS

basicSpec :: PrefixMap -> AParser st BASIC_SPEC
basicSpec _ =
  fmap Basic_spec (trailingAnnosParser basicItem)
  <|>
  (oBraceT >> cBraceT >> return (Basic_spec []))

basicItem :: AParser st BASIC_ITEM
basicItem =
 do d <- tokensP twelfMultDeclChars
    dotT
    return $ Decl $ trim d
 <|>
 do dotT
    f <- tokensP twelfMultDeclChars
    return $ Form $ trim f

tokenP :: String -> AParser st String
tokenP chars = reserved criticalKeywords $
   many1 $ scanLPD <|> oneOf chars

tokensP :: String -> AParser st String
tokensP chars = do
  ss <- many1 (tokenP chars <|> whitesp)
  return $ concat ss

whitesp :: AParser st String
whitesp = many1 $ oneOf whiteChars

symbItems :: AParser st SYMB_ITEMS
symbItems = fmap (Symb_items . fst) $
   tokenP twelfSymChars `separatedBy` anComma

symbMapItems :: AParser st SYMB_MAP_ITEMS
symbMapItems = fmap (Symb_map_items . fst) $
  symbOrMap `separatedBy` anComma

symbOrMap :: AParser st SYMB_OR_MAP
symbOrMap = do
  s <- tokenP twelfSymChars
  (do asKey mapsTo
      t <- tokensP twelfDeclChars
      return $ Symb_map s $ trim t)
    <|>
    return (Symb s)

trim :: String -> String
trim = let f = reverse . dropWhile isSpace
           in f . f
