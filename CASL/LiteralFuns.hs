{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich and Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  experimental
Portability :  portable 

functions to test ids with argument terms for literals of CASL
-}

module CASL.LiteralFuns ( isLiteral
                        , isNumber
                        , isFrac
                        , isFloat
                        , isString
                        , isList
                        , splitAppl
                        , splitApplM
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

isString :: GlobalAnnos -> Id -> [TERM f] -> Bool
isString = isGenString splitApplM

isList :: GlobalAnnos -> Id -> [TERM f] -> Bool
isList = isGenList splitApplM

isFloat :: GlobalAnnos -> Id -> [TERM f] -> Bool
isFloat = isGenFloat splitApplM

isFrac :: GlobalAnnos -> Id -> [TERM f] -> Bool
isFrac = isGenFrac splitApplM

splitApplM :: TERM f -> Maybe (Id, [TERM f])
splitApplM t = case t of
    Application (Op_name _) _ _ -> Just $ splitAppl t 
    _ -> Nothing

splitAppl :: TERM f -> (Id, [TERM f])
splitAppl t = case t of
              Application oi ts _ -> (op_id oi,ts)
              _ -> error "splitAppl: no Application found"

op_id :: OP_SYMB -> Id
op_id op = case op of 
           Qual_op_name _ _ _ -> 
               error "cannot literally Print Qual_id" 
           Op_name x          -> x

isQualOpSy :: OP_SYMB -> Bool
isQualOpSy o = case o of
           Op_name _          -> False
           Qual_op_name _ _ _ -> True
