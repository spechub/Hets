{- |
Module      :  ./TIP/Utils.hs
Description :  utility functions for dealing with TIP objects
Copyright   :  (c) Tom Kranz 2022
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :
Stability   :  experimental
Portability :  non-portable (imports TIP.AbsTIP)

Extracting/wrapping names and attributes from/in TIP objects, with quoting.
-}
module TIP.Utils where

import TIP.AbsTIP
import TIP.PrintTIP (printTree)
import Data.Maybe
import Data.Char
import Data.Set hiding (filter,map)
import Data.Function

printTIP :: Start -> String
printTIP (Start ds) = unlines $ map (\d -> "("++printTree d++")") ds

unquotedLaterSymbols :: Set Char
unquotedLaterSymbols = fromList "~!@$%^&*_-+=<>.?/"

isUnquotedLaterSymbol :: Char -> Bool
isUnquotedLaterSymbol = (flip member) unquotedLaterSymbols

unquotedInitialSymbols :: Set Char
unquotedInitialSymbols = fromList "~!@$%^&*_+=<>.?/"

isUnquotedInitialSymbol :: Char -> Bool
isUnquotedInitialSymbol = (flip member) unquotedInitialSymbols

anyOf :: a -> [a -> Bool] -> Bool
anyOf c = any (c &)

getFormulaName :: Decl -> Maybe String
getFormulaName (Formula _ attrs _) = listToMaybe $ getAttrValues ":axiom" attrs
getFormulaName (FormulaPar _ attrs _ _) = listToMaybe $ getAttrValues ":axiom" attrs
getFormulaName _ = Nothing

getAttrValues :: String -> [Attr] -> [String]
getAttrValues skey = mapMaybe $ getAttrValue skey

getAttrValue :: String -> Attr -> Maybe String
getAttrValue skey attr
  | (Value (Keyword akey) sym) <- attr
  , (akey == skey)
  = Just $ fromSymbol sym
  | otherwise = Nothing

addAttr :: Decl -> (String, Maybe String) -> Decl
addAttr (Formula assertion attrs expr) kv = Formula assertion (toAttr kv : attrs) expr
addAttr (FormulaPar assertion attrs par expr) kv = FormulaPar assertion (toAttr kv : attrs) par expr
addAttr other _ = other

stripAttrs :: Decl -> Decl
stripAttrs (Formula assertion _ expr) = Formula assertion [] expr
stripAttrs (FormulaPar assertion _ par expr) = FormulaPar assertion [] par expr
stripAttrs other = other

declareData :: [(DatatypeName, Datatype)] -> [Decl]
declareData [] = []
declareData ((DatatypeName n _,t):[]) = [DeclareDatatype n t]
declareData plural = [DeclareDatatypes (map fst plural) (map snd plural)]

singularizeDatas :: Decl -> [Decl]
singularizeDatas (DeclareDatatypes dns dts) = concatMap (declareData.(:[])) $ zip dns dts
singularizeDatas d = d:[]

fromSymbol :: Symbol -> String
fromSymbol (Unquoted (UnquotedSymbol (_, sym))) = sym
fromSymbol (Quoted (QuotedSymbol (_, sym))) = unquoteSymbolChars $ init $ tail sym

toAttr :: (String, Maybe String) -> Attr
toAttr (key, mValue)
  | Just value <- mValue = Value kw $ toSymbol value
  | otherwise = NoValue kw
    where kw = (Keyword $ ':' : filter ((flip anyOf) [isLetter,isDigit,(=='-')]) key)

quoteSymbolChar :: Char -> String
quoteSymbolChar '\\' = "\\\\"
quoteSymbolChar '|' = "\\|"
quoteSymbolChar c = [c]

unquoteSymbolChars :: String -> String
unquoteSymbolChars ('\\' : c : cs) = c : unquoteSymbolChars cs
unquoteSymbolChars (c : cs) = c : unquoteSymbolChars cs
unquoteSymbolChars [] = []

toSymbol :: String -> Symbol
toSymbol s
  | (h : t) <- s
  , anyOf h [isUnquotedInitialSymbol, isLetter]
  , all ((flip anyOf) [isUnquotedLaterSymbol, isDigit, isLetter]) t
  = Unquoted $ UnquotedSymbol ((0,0),s)
  | otherwise
  = Quoted $ QuotedSymbol ((0,0),"|" ++ concatMap quoteSymbolChar s ++ "|")
