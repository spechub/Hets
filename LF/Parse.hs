{- |
Module      :  $Header$
Description :  A parser for the Edinburgh Logical Framework
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2010
License     :  GPLv2 or higher

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

import Data.Char

import LF.AS

twelfNameChars :: String
twelfNameChars = "_-+*/<=>@^"

twelfTokenChars :: String
twelfTokenChars = twelfNameChars ++ ":{}[]()"

trim :: String -> String
trim = let f = reverse . dropWhile isSpace
           in f . f

basicSpec :: AParser st BASIC_SPEC
basicSpec =
  fmap Basic_spec (trailingAnnosParser basicItem)
  <|>
  (oBraceT >> cBraceT >> return (Basic_spec []))

basicItem :: AParser st BASIC_ITEM
basicItem = do
 do d <- twelfStat
    dotT
    return $ Decl $ trim d
 <|>
 do dotT
    f <- twelfStat
    return $ Form $ trim f

twelfStat :: AParser st String
twelfStat = do ss <- many1 (twelfToken <|> whiteSp)
               return $ concat ss

twelfToken :: AParser st String
twelfToken = reserved criticalKeywords $
               many1 $ scanLPD <|> oneOf twelfTokenChars

twelfName :: AParser st String
twelfName = reserved criticalKeywords $
              many1 $ scanLPD <|> oneOf twelfNameChars

whiteSp :: AParser st String
whiteSp = many1 $ oneOf whiteChars

symbItems :: AParser st SYMB_ITEMS
symbItems = fmap Symb_items $ fmap fst $ twelfName `separatedBy` anComma

symbMapItems :: AParser st SYMB_MAP_ITEMS
symbMapItems = do
  (xs, _) <- symbOrMap `separatedBy` anComma
  return $ Symb_map_items xs

symbOrMap :: AParser st SYMB_OR_MAP
symbOrMap = do
  s <- twelfName
  ( do asKey mapsTo
       t <- twelfStat
       return $ Symb_map s t
    <|>
    return (Symb s) )
