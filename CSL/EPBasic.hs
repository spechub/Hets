{- |
Module      :  $Header$
Description :  Some basic types for Extended Parameters
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  experimental
Portability :  portable

This module defines some basic types for Extended Parameters
 -}

module CSL.EPBasic where

import Data.List
-- ----------------------------------------------------------------------
-- * General Datatypes for Extended Parameters
-- ----------------------------------------------------------------------

data BoolRep = Not BoolRep | Impl BoolRep BoolRep | And [BoolRep]
             | Or [BoolRep] | Pred String [String]


-- ----------------------------------------------------------------------
-- * Output for SMT
-- ----------------------------------------------------------------------


smtBoolExp :: BoolRep -> String
smtBoolExp br = let f s l = g s smtBoolExp l
                    g s h l = concat ["(", intercalate " " $ s : map h l, ")"]
                in case br of
                     Not b -> f "not" [b]
                     Impl b1 b2 -> f "=>" [b1, b2]
                     And l -> f "and" l
                     Or l -> f "or" l
                     Pred s l -> g s id l
