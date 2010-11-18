{- |
Module      :  $Header$
Description :  Some basic types for simple boolean representations
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  experimental
Portability :  portable

This module defines some basic types for a simple boolean representation and
a printer which outputs this representation into an s-expression like format.
This is mainly for communication with the smt-solver yices.
 -}

module CSL.EPBasic where

import Data.List
-- ----------------------------------------------------------------------
-- * General Datatypes for Extended Parameters
-- ----------------------------------------------------------------------

data BoolRep = Not BoolRep | Impl BoolRep BoolRep | And [BoolRep]
             | Or [BoolRep] | Pred String [String]


trueBool :: BoolRep
trueBool = Pred "true" []

falseBool :: BoolRep
falseBool = Pred "false" []

mapPred :: (String -> [String] -> BoolRep) -> BoolRep -> BoolRep
mapPred f br =
    case br of
      Not x -> Not $ mapPred f x
      Impl x y -> Impl (mapPred f x) $ mapPred f y
      And l -> And $ map (mapPred f) l
      Or l -> Or $ map (mapPred f) l
      Pred s l -> f s l

-- ----------------------------------------------------------------------
-- * Output for SMT
-- ----------------------------------------------------------------------


smtBoolExp :: BoolRep -> String
smtBoolExp br = let f s l = g s smtBoolExp l
                    g s _ [] = s
                    g s h l = concat ["(", intercalate " " $ s : map h l, ")"]
                in case br of
                     Not b -> f "not" [b]
                     Impl b1 b2 -> f "=>" [b1, b2]
                     And l -> f "and" l
                     Or l -> f "or" l
                     Pred s l -> g s id l
