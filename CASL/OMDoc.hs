{- |
Module      :  $Header$
Description :  CASL specific OMDoc constants
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2009
License     :  GPLv2 or higher

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  provisional
Portability :  portable

Library of CASL specific OMDoc constants
-}

module CASL.OMDoc where

import OMDoc.DataTypes

-- * Meta theory

-- | CASL meta theory content dictionary
caslMetaTheory :: OMCD
caslMetaTheory = CD ["casl", "http://cds.omdoc.org/logics/casl/casl.omdoc"]


-- * Terms

-- cdbase entries missing for predefined content dictionaries

const_casl :: String -> OMElement
const_casl n = OMS (caslMetaTheory, mkSimpleName n)

const_true, const_false, const_sort, const_funtype, const_partialfuntype
 , const_and, const_or, const_implies, const_implied, const_equivalent
 , const_forall, const_exists, const_eq, const_eeq, const_existsunique
 , const_def, const_in, const_if, const_cast, const_type, const_not
 , const_predtype, const_subsortof :: OMElement

const_true = const_casl "true"
const_false = const_casl "false"

const_funtype = const_casl "funtype"
const_partialfuntype = const_casl "partialfuntype"
const_predtype = const_casl "predtype"
const_type = const_casl "type"
const_subsortof = const_casl "subsortof"

const_not = const_casl "not"
const_and = const_casl "and"
const_or = const_casl "or"
const_implies = const_casl "implies"
const_implied = const_casl "implied"
const_equivalent = const_casl "equivalent"

const_forall = const_casl "forall"
const_exists = const_casl "exists"

const_eq = const_casl "eq"
const_eeq = const_casl "eeq"
const_existsunique = const_casl "existsunique"
const_def = const_casl "def"
const_in = const_casl "in"
const_if = const_casl "if"
const_cast = const_casl "cast"
const_sort = const_casl "sort"

