module CommonLogic.OMDoc where

import OMDoc.DataTypes


clMetaTheory = CD ["commonlogic", "http://cds.omdoc.org/logics/commonlogic.omdoc"]

const_cl :: String -> OMElement
const_cl n = OMS (clMetaTheory, mkSimpleName n)


const_symbol, const_forall, const_exists, const_and, const_or
 , const_not, const_implies, const_equivalent, const_eq, const_comment 
 , const_irregular, const_comment_term :: OMElement 

const_symbol = const_cl "symbol"
const_forall = const_cl "forall"
const_exists = const_cl "exists"
const_and = const_cl "and"
const_or = const_cl "or"
const_not = const_cl "not"
const_implies = const_cl "implies"
const_equivalent = const_cl "equivalent"
const_eq = const_cl "eq"
const_comment = const_cl "comment"
const_irregular = const_cl "irregular"
const_comment_term = const_cl "comment_term"
