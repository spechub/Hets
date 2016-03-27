{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./Fpl/Sign.hs
Description :  signatures for FPL
Copyright   :  (c) Christian Maeder, DFKI GmbH 2011
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

signature extension for FPL to keep track of constructors
-}

module Fpl.Sign where

import Fpl.As

import Common.AS_Annotation
import Common.Doc
import Common.DocUtils
import Common.Id
import Common.Keywords
import qualified Common.Lib.MapSet as MapSet
import qualified Common.Lib.Rel as Rel

import CASL.Sign
import CASL.AS_Basic_CASL
import CASL.ToDoc

import Data.Data
import Data.List
import Data.Ord

boolSort :: Id
boolSort = stringToId "Bool"

trueC :: Id
trueC = stringToId trueS

falseC :: Id
falseC = stringToId falseS

boolType :: OpType
boolType = sortToOpType boolSort

data SignExt = SignExt
  { constr :: OpMap }
  deriving (Show, Eq, Ord, Typeable, Data)

instance Pretty SignExt where
  pretty es = let nr = nullRange in case
         groupBy (\ (_, c1) (_, c2) -> opRes c1 == opRes c2)
         $ sortBy (comparing (opRes . snd))
         $ mapSetToList $ constr es of
     [] -> empty
     l -> topSigKey (sortS ++ appendS l) <+> sepBySemis
       (map (\ g -> printDD
             (Datatype_decl (opRes $ snd $ head g)
              (map (\ (i, t) -> emptyAnno $
                    Alt_construct Total i (map Sort $ opArgs t) nr)
               g) nr)) l)

emptyFplSign :: SignExt
emptyFplSign = SignExt MapSet.empty

diffFplSign :: SignExt -> SignExt -> SignExt
diffFplSign a b = a
  { constr = constr a `diffOpMapSet` constr b }

addFplSign :: SignExt -> SignExt -> SignExt
addFplSign a b = a
  { constr = addOpMapSet (constr a) $ constr b }

interFplSign :: SignExt -> SignExt -> SignExt
interFplSign a b = a
  { constr = interOpMapSet (constr a) $ constr b }

isSubFplSign :: SignExt -> SignExt -> Bool
isSubFplSign s1 s2 = isSubOpMap (constr s1) (constr s2)

type FplSign = Sign TermExt SignExt

addBools :: OpMap -> OpMap
addBools = addOpTo falseC boolType . addOpTo trueC boolType

addConsts :: SignExt -> SignExt
addConsts s = s { constr = addBools $ constr s }

addBuiltins :: FplSign -> FplSign
addBuiltins s = s { sortRel = Rel.insertKey boolSort $ sortRel s
                  , opMap = addBools $ opMap s
                  , extendedInfo = addConsts $ extendedInfo s }

delBuiltins :: FplSign -> FplSign
delBuiltins s = diffSig diffFplSign s $ addBuiltins $ emptySign emptyFplSign
