{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich and Uni Bremen 2002-2003 
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  experimental
Portability :  portable 

functions to test ids with argument terms for literals of CASL
-}


module CASL.LiteralFuns ( isLiteral
                        , isNumber
                        , isSignedNumber
                        , isString
                        , isList
                        , isFloat
                        , isFrac
                        , collectElements
                        , basicTerm
                        , convCASLChar
                        , splitAppl
                        , op_id
                        , isQualOpSy
                        ) where

import Common.Id
import Common.GlobalAnnotations
import Common.ConvertLiteral 
import CASL.AS_Basic_CASL

isLiteral :: GlobalAnnos -> Id -> [TERM f] -> Bool
isLiteral = isGenLiteral splitApplM

isNumber :: GlobalAnnos -> Id -> [TERM f] -> Bool
isNumber = isGenNumber splitApplM

isSignedNumber :: GlobalAnnos -> Id -> [TERM f] -> Bool
isSignedNumber = isGenSignedNumber splitApplM

isString :: GlobalAnnos -> Id -> [TERM f] -> Bool
isString = isGenString splitApplM

convCASLChar :: Token -> String
convCASLChar t = case tokStr t of
                 cs | not (null cs) && head cs == '\''
                      && last cs == '\'' -> init $ tail cs
                    | otherwise -> 
                        error ("convCASLChar: " ++ cs ++
                               " is not a valid CASL Char")

isList :: GlobalAnnos -> Id -> [TERM f] -> Bool
isList = isGenList splitApplM

isFloat :: GlobalAnnos -> Id -> [TERM f] -> Bool
isFloat = isGenFloat splitApplM

isFrac :: GlobalAnnos -> Id -> [TERM f] -> Bool
isFrac = isGenFrac splitApplM

splitApplM :: TERM f -> Maybe (Id, [TERM f])
splitApplM t = if isAppl t then Just $ splitAppl t else Nothing

isAppl :: TERM f -> Bool
isAppl t = case t of
              Application (Op_name _) _ _ -> True
              _ -> False

splitAppl :: TERM f -> (Id,[TERM f])
splitAppl t = case t of
              Application oi ts _ -> (op_id oi,ts)
              _ -> error "splitAppl: no Application found"


leftAssCollElems :: Id -> [TERM f] -> [TERM f]
leftAssCollElems i trs = 
     case trs of
              []    -> error "no elements to collect"
              [x]   -> [x]
              [x,y] -> leftAssCollElems i (splitA x) ++ [y]
              _ys   -> error "too many elements to collect"
    where splitA t = case t of
                          Application oi its _ 
                              | op_id oi == i -> its
                              | otherwise     -> [t]
                          _        -> error "splitA: no Appl found (left)"

collectElements :: (Maybe Id) -> Id -> [TERM f] -> [TERM f]
collectElements mnid i trs = 
    if detect_left_ass i trs 
    then leftAssCollElems i trs
    else collectElementsRight mnid i trs

detect_left_ass :: Id -> [TERM f] -> Bool
detect_left_ass i trs = 
    case trs of
    []    -> True
    [_]   -> False
    [x,_] ->  case x of
          Application oi _ _ -> op_id oi == i
          _        -> False           
    _     -> False

collectElementsRight :: (Maybe Id) -> Id -> [TERM f] -> [TERM f]
collectElementsRight mnid i trs = 
     case trs of
              []    -> error "no elements to collect"
              [x]   -> getToken x
              [x,y] -> x : collectElementsRight mnid i (splitA y)
              _ys   -> error "too many elements to collect"
    where splitA t = case t of
                          Application oi its _ 
                              | op_id oi == i -> its
                              | otherwise     -> [t]
                          _        -> error "splitA: no Appl found (right)"
          getToken :: TERM f -> [TERM f]
          getToken trm = maybe [trm]
                               (\ nid -> case trm of
                                     Application oid [] _ 
                                         | op_id oid == nid -> []
                                         | otherwise -> 
                                             error "null element not found"
                                     _ -> error "no Application found") 
                               mnid

basicTerm :: TERM f -> Maybe Token
basicTerm trm = case trm of
                Application oi [] _ -> 
                    case op_id oi of
                    Id [tok] [] _ -> Just tok
                    _    -> error "wrong Id for getToken"
                Application _oi _ats _ -> Nothing
                _   -> error "wrong TERM for basicTerm" 

op_id :: OP_SYMB -> Id
op_id op = case op of 
           Qual_op_name _ _ _ -> 
               error "cannot literally Print Qual_id" 
           Op_name x          -> x

isQualOpSy :: OP_SYMB -> Bool
isQualOpSy o = case o of
	   Op_name _          -> False
	   Qual_op_name _ _ _ -> True
