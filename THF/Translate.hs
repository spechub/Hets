{- |
Module      :  $Header$
Description :  create legal THF mixfix identifier
Copyright   :  (c) A. Tsogias, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Alexis.Tsogias@dfki.de
Stability   :  provisional
Portability :  portable

translate 'Id' to THF Constant
-}

module THF.Translate where

import Common.Id
import Common.Result

import HasCASL.Builtin
import HasCASL.AsUtils

import THF.As as THFAs

import Data.Char
import qualified Data.Map as Map


mkTypesName :: THFAs.Constant -> THFAs.Name
mkTypesName c = case c of
    A_Lower_Word w -> N_Atomic_Word $ A_Lower_Word ("type_" ++ w)
    A_Single_Quoted s -> N_Atomic_Word $ A_Single_Quoted ("type_" ++ s)

mkConstsName :: THFAs.Constant -> THFAs.Name
mkConstsName c = case c of
    A_Lower_Word w -> N_Atomic_Word $ A_Lower_Word ("const_" ++ w)
    A_Single_Quoted s -> N_Atomic_Word $ A_Single_Quoted ("const_" ++ s)

mkDefName :: THFAs.Constant -> THFAs.Name
mkDefName c = case c of
    A_Lower_Word w -> N_Atomic_Word $ A_Lower_Word ("def_" ++ w)
    A_Single_Quoted s -> N_Atomic_Word $ A_Single_Quoted ("def_" ++ s)

transTypeId :: Id -> Result THFAs.Constant
transTypeId id1 = case maybeElem id1 preDefHCTypeIds of
    Just res -> return $ stringToConstant res
    Nothing  -> case transToTHFString $ show id1 of
        Just s  -> return $ stringToConstant s
        Nothing -> fatal_error ("Unable to translate " ++ show id1 ++
            " into a THF valide Constant.") nullRange

transAssumpId :: Id -> Result THFAs.Constant
transAssumpId id1 = case maybeElem id1 preDefHCAssumpIds of
    Just res -> return $ stringToConstant res
    Nothing  -> case transToTHFString $ show id1 of
        Just s  -> return $ stringToConstant s
        Nothing -> fatal_error ("Unable to translate " ++ show id1 ++
            " into a THF valide Constant.") nullRange

transAssumpsId :: Id -> Int -> Result THFAs.Constant
transAssumpsId id1 int = if int == 1 then transAssumpId id1 else
    case transToTHFString $ show id1 of
        Just s  -> return $ stringToConstant (s ++ show int)
        Nothing -> fatal_error ("Unable to translate " ++ show id1 ++
            " into a THF valide Constant.") nullRange

stringToConstant :: String -> THFAs.Constant
stringToConstant = A_Lower_Word . stringToLowerWord

stringToLowerWord :: String -> THFAs.LowerWord
stringToLowerWord (c1 : rc)  = toLower c1 : rc
stringToLowerWord [] = []

stringToVariable :: String -> THFAs.Variable
stringToVariable (c1 : rc) = toUpper c1 : rc
stringToVariable [] = []

transVarId :: Id -> Result THFAs.Variable
transVarId id1 = case transToTHFString $ show id1 of
        Just s  -> return $ stringToVariable s
        Nothing -> fatal_error ("Unable to translate " ++ show id1 ++
            " into a THF valide Variable.") nullRange

transToTHFString :: String -> Maybe String
transToTHFString s = case s of
    []       -> Just []
    (c : rc) ->
        if isTHFChar c
        then fmap (c :) (transToTHFString rc)
        else case Map.lookup c charMap of
            Just res -> fmap (res ++) (transToTHFString rc)
            Nothing  -> Nothing

isTHFChar :: Char -> Bool
isTHFChar c = (isAlphaNum c && isAscii c) || c == '_'

isLowerTHFChar :: Char -> Bool
isLowerTHFChar c = isLower c && isAscii c

preDefHCTypeIds :: Map.Map Id String
preDefHCTypeIds = Map.fromList
    [ (logId,                   "hct" ++ show logId)
    , (predTypeId,              "hct" ++ show predTypeId)
    , (unitTypeId,              "hct" ++ show unitTypeId)
    , (lazyTypeId,              "hctLazy")
    , (arrowId FunArr,          "hct__FunArr__")
    , (arrowId PFunArr,         "hct__PFunArr__")
    , (arrowId ContFunArr,      "hct__ContFunArr__")
    , (arrowId PContFunArr,     "hct__PContFunArr__")
    , (productId 2 nullRange,   "hct__X__")
    , (productId 3 nullRange,   "hct__X__X__")
    , (productId 4 nullRange,   "hct__X__X__X__")
    , (productId 5 nullRange,   "hct__X__X__X__X__") ]

preDefHCAssumpIds :: Map.Map Id String
preDefHCAssumpIds = Map.fromList
    [ (botId,       "hcc" ++ show botId)
    , (defId,       "hcc" ++ show defId)
    , (notId,       "hcc" ++ show notId)
    , (negId,       "hccNeg__")
    , (whenElse,    "hcc" ++ show whenElse)
    , (trueId,      "hcc" ++ show trueId)
    , (falseId,     "hcc" ++ show falseId)
    , (eqId,        "hcc__Eq__")
    , (exEq,        "hcc__ExEq__")
    , (resId,       "hcc" ++ show resId)
    , (andId,       "hcc__And__")
    , (orId,        "hcc__Or__")
    , (eqvId,       "hcc__Eqv__")
    , (implId,      "hcc__Impl__")
    , (infixIf,     "hcc" ++ show infixIf) ]

maybeElem :: Id -> Map.Map Id a -> Maybe a
maybeElem id1 m = helper id1 (Map.toList m)
    where
        helper :: Id -> [(Id, a)] -> Maybe a
        helper _ [] = Nothing
        helper id2 ((eid, ea) : r) =
            if myEqId id2 eid then Just ea else helper id2 r

myEqId :: Id -> Id -> Bool
myEqId (Id t1 c1 _) (Id t2 c2 _) = (t1, c1) == (t2, c2)

-- | a separate Map speeds up lookup
charMap :: Map.Map Char String
charMap = Map.fromList
 [(' ' , "Space"),
  ('\n', "Newline"),
  ('\t', "Tab"),
  ('!' , "Exclam"),
  ('"' , "Quot"),
  ('#' , "Hash"),
  ('$' , "Dollar"),
  ('%' , "Percent"),
  ('&' , "Amp"),
  ('\'', "Apostrophe"),
  ('(' , "OBr"),
  (')' , "CBr"),
  ('*' , "X"),
  ('+' , "Plus"),
  (',' , "Comma"),
  ('-' , "Minus"),
  ('.' , "Dot"),
  ('/' , "Slash"),
  (':' , "Colon"),
  (';' , "Semi"),
  ('<' , "Lt"),
  ('=' , "Eq"),
  ('>' , "Gt"),
  ('?' , "Quest"),
  ('@' , "At"),
  ('[' , "OSqBr"),
  ('\\' , "Bslash"),
  (']' , "CSqBr"),
  ('^' , "Caret"), -- Hat?
  ('`' , "Grave"),
  ('{' , "LBrace"),
  ('|' , "VBar"),
  ('}' , "RBrace"),
  ('~' , "Tilde"),
  ('\160', "Nbsp"),
  ('\161', "Iexcl"),
  ('\162', "Cent"),
  ('\163', "Pound"),
  ('\164', "Curren"),
  ('\165', "Yen"),
  ('\166', "Brvbar"),
  ('\167', "Sect"),
  ('\168', "Uml"),
  ('\169', "Copy"),
  ('\170', "Ordf"),
  ('\171', "Laquo"),
  ('\172', "Not"),
  ('\173', "Shy"),
  ('\174', "Reg"),
  ('\175', "Macr"),
  ('\176', "Deg"),
  ('\177', "Plusmn"),
  ('\178', "Sup2"),
  ('\179', "Sup3"),
  ('\180', "Acute"),
  ('\181', "Micro"),
  ('\182', "Para"),
  ('\183', "Middot"),
  ('\184', "Cedil"),
  ('\185', "Sup1"),
  ('\186', "Ordm"),
  ('\187', "Raquo"),
  ('\188', "Quarter"),
  ('\189', "Half"),
  ('\190', "Frac34"),
  ('\191', "Iquest"),
  ('\192', "Agrave"),
  ('\193', "Aacute"),
  ('\194', "Acirc"),
  ('\195', "Atilde"),
  ('\196', "Auml"),
  ('\197', "Aring"),
  ('\198', "AElig"),
  ('\199', "Ccedil"),
  ('\200', "Egrave"),
  ('\201', "Eacute"),
  ('\202', "Ecirc"),
  ('\203', "Euml"),
  ('\204', "Igrave"),
  ('\205', "Iacute"),
  ('\206', "Icirc"),
  ('\207', "Iuml"),
  ('\208', "ETH"),
  ('\209', "Ntilde"),
  ('\210', "Ograve"),
  ('\211', "Oacute"),
  ('\212', "Ocirc"),
  ('\213', "Otilde"),
  ('\214', "Ouml"),
  ('\215', "Times"),
  ('\216', "OSlash"),
  ('\217', "Ugrave"),
  ('\218', "Uacute"),
  ('\219', "Ucirc"),
  ('\220', "Uuml"),
  ('\221', "Yacute"),
  ('\222', "THORN"),
  ('\223', "Szlig"),
  ('\224', "Agrave"),
  ('\225', "Aacute"),
  ('\226', "Acirc"),
  ('\227', "Atilde"),
  ('\228', "Auml"),
  ('\229', "Aring"),
  ('\230', "Aelig"),
  ('\231', "Ccedil"),
  ('\232', "Egrave"),
  ('\233', "Eacute"),
  ('\234', "Ecirc"),
  ('\235', "Euml"),
  ('\236', "Igrave"),
  ('\237', "Iacute"),
  ('\238', "Icirc"),
  ('\239', "Iuml"),
  ('\240', "Eth"),
  ('\241', "Ntilde"),
  ('\242', "Ograve"),
  ('\243', "Oacute"),
  ('\244', "Ocirc"),
  ('\245', "Otilde"),
  ('\246', "Ouml"),
  ('\247', "Divide"),
  ('\248', "Oslash"),
  ('\249', "Ugrave"),
  ('\250', "Uacute"),
  ('\251', "Ucirc"),
  ('\252', "Uuml"),
  ('\253', "Yacute"),
  ('\254', "Thorn"),
  ('\255', "Yuml")]
