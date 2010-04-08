{- |
Module      :  $Header$
Description :  Hets-to-OMDoc conversion
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

CASL implementation of the interface functions export_signToOmdoc,
export_morphismToOmdoc, export_senToOmdoc from class Logic. The actual
instantiation can be found in module CASL.Logic_CASL.
-}

module CASL.OMDocImport
    ( omdocToSym
    , omdocToSen
    ) where

import OMDoc.DataTypes
--import OMDoc.Export

import Common.Id
import Common.Result
import Common.AS_Annotation
--import qualified Common.Lib.Rel as Rel

import CASL.AS_Basic_CASL
import CASL.Sign
--import CASL.Fold
--import CASL.Quantification
import CASL.OMDoc

import qualified Data.Map as Map
import Data.Maybe

-- * Environment Interface

type Env = SigMapI Symbol

symbolToSort :: Symbol -> SORT
symbolToSort (Symbol n SortAsItemType) = n
symbolToSort _ = error "symbolToSort: Nonsort encountered"

symbolToOp :: Symbol -> (Id, OpType)
symbolToOp (Symbol n (OpAsItemType ot)) = (n, ot)
symbolToOp _ = error "symbolToOp: Nonop encountered"

symbolToPred :: Symbol -> (Id, PredType)
symbolToPred (Symbol n (PredAsItemType pt)) = (n, pt)
symbolToPred _ = error "symbolToPred: Nonpred encountered"

lookupSymbol :: Env -> OMName -> Symbol
lookupSymbol e omn = 
    Map.findWithDefault (error $ "lookupSymbol failed for: " ++ show omn ++ " map " ++ (show $ sigMapISymbs e))
       omn $ sigMapISymbs e

lookupSort :: Env -> OMName -> SORT
lookupSort e = symbolToSort . lookupSymbol e

lookupSortOMS :: String -> Env -> OMElement -> SORT
lookupSortOMS msg e oms@(OMS (cd, omn)) =
    if cdIsEmpty cd then lookupSort e omn
    else error $ concat [ msg, ": lookupSortOMS: Nonempty cd in const: "
                        , show oms]
lookupSortOMS msg _ ome =
    error $ concat [msg, ": lookupSortOMS: Nonsymbol: ", show ome]


-- * Hets utils

nameToId :: String -> Id
nameToId s = mkId [mkSimpleId s]

-- * TOPLEVEL Interface

-- | A TCSymbols is transformed to a CASL symbol with given name.
omdocToSym :: Env -> TCElement -> String -> Result Symbol
omdocToSym e sym@(TCSymbol _ ctp srole _) n =
    case srole of
      Typ | ctp == const_sort -> return $ idToSortSymbol $ nameToId n
          | otherwise -> fail $ "omdocToSym: No sorttype for " ++ show sym
      Obj -> return $
             case omdocToType e ctp of
               Left ot -> idToOpSymbol (nameToId n) ot
               Right pt -> idToPredSymbol (nameToId n) pt
      _ -> fail $ concat [ "omdocToSym: only type or object are allowed as"
                         , " symbol roles, but found: ", show srole ]

omdocToSym _ sym _ = fail $ concat [ "omdocToSym: only TCSymbol is allowed,"
                                   , " but found: ", show sym ]


omdocToSen :: Env -> TCElement -> String
           -> Result (Maybe (Named (FORMULA f)))
omdocToSen _ _ _ = return Nothing


-- * Types

omdocToType :: Env -> OMElement -> Either OpType PredType
omdocToType e (OMA (c:args)) =
    let sorts = map (lookupSortOMS "omdocToType" e) args
        opargs = init sorts
        oprange = last sorts
        res | c == const_predtype = Right $ PredType sorts
            | c == const_partialfuntype = Left $ OpType Partial opargs oprange
            | c == const_funtype = Left $ OpType Total opargs oprange
            | otherwise = error $ "omdocToType: unknown type constructor: "
                          ++ show c
    in res

omdocToType e oms@(OMS _) =
    Left $ OpType Total [] $ lookupSortOMS "omdocToType" e oms

omdocToType _ ome = error $ "omdocToType: Non-supported element: " ++ show ome


-- * Terms
{-




data TERM f = Qual_var VAR SORT Range -- pos: "(", var, colon, ")"
          | Application OP_SYMB [TERM f] Range
            -- pos: parens around TERM f if any and seperating commas
          | Sorted_term (TERM f) SORT Range
            -- pos: colon
          | Cast (TERM f) SORT Range
            -- pos: "as"
          | Conditional (TERM f) (FORMULA f) (TERM f) Range

-}
