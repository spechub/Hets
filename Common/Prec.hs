{- |
Module      :  $Header$
Description :  precedence checking
Copyright   :  Christian Maeder and Uni Bremen 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

Precedence checking
-}

module Common.Prec where

import Common.Id
import Common.GlobalAnnotations
import Common.AS_Annotation
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Common.Lib.Rel as Rel

-- | a precedence map using numbers for faster lookup
data PrecMap = PrecMap
    { precMap :: Map.Map Id Int
    , maxWeight :: Int
    } deriving Show

emptyPrecMap :: PrecMap
emptyPrecMap = PrecMap
    { precMap = Map.empty
    , maxWeight = 0
    }

mkPrecIntMap :: Rel.Rel Id -> PrecMap
mkPrecIntMap r =
    let (m, t) = Rel.toPrecMap r
        in emptyPrecMap
               { precMap = m
               , maxWeight = t
               }

getIdPrec :: PrecMap -> Set.Set Id -> Id -> Int
getIdPrec p ps i = let PrecMap m mx = p in
    if i == applId then mx + 1
    else Map.findWithDefault
    (if begPlace i || endPlace i then
         if Set.member i ps then Map.findWithDefault (div mx 2) eqId m else mx
     else mx + 2) i m

getSimpleIdPrec :: PrecMap -> Id -> Int
getSimpleIdPrec p = getIdPrec p Set.empty

-- | drop as many elements as are in the first list
dropPrefix :: [a] -> [b] -> [b]
dropPrefix [] l = l
dropPrefix _ [] = []
dropPrefix (_ : xs) (_ : ys) = dropPrefix xs ys

-- | check if a left argument will be added.
-- (The 'Int' is the number of current arguments.)
isLeftArg :: Id -> [a] -> Bool
isLeftArg op nArgs = null nArgs && begPlace op
-- | check if a right argument will be added.
isRightArg :: Id -> [a] -> Bool
isRightArg op@(Id toks _ _) nArgs = endPlace op &&
    (isSingle $ dropPrefix nArgs $ filter isPlace toks)

joinPlace :: AssocEither -> Id -> Bool
joinPlace side = case side of
    ALeft -> begPlace
    ARight -> endPlace

checkArg :: AssocEither -> GlobalAnnos -> (Id, Int) -> (Id, Int) -> Id -> Bool
checkArg side ga (op, opPrec) (arg, argPrec) weight =
    let precs = prec_annos ga
        assocs = assoc_annos ga
        junction = joinPlace side arg
    in if argPrec <= 0 then False
       else case compare argPrec opPrec of
           LT -> not junction && op /= applId
           GT -> True
           EQ -> if junction then
               case precRel precs op weight of
               Lower -> True
               Higher -> False
               BothDirections -> False
               NoDirection ->
                   case (isInfix arg, joinPlace side op) of
                        (True, True) -> if arg == op
                                        then not $ isAssoc side assocs op
                                        else True
                        (False, True) -> True
                        (True, False) -> False
                        _ -> side == ALeft
            else True

-- | compute the left or right weight for the application
nextWeight :: AssocEither -> GlobalAnnos -> Id -> Id -> Id
nextWeight side ga arg op =
       if joinPlace side arg then
          case precRel (prec_annos ga) op arg of
            Higher -> arg
            _ -> op
       else op

-- | check precedence of an argument and a top-level operator.
checkPrec :: GlobalAnnos -> (Id, Int) -> (Id, Int) -> [a] ->
             (AssocEither -> Id) -> Bool
checkPrec ga op@(o, _) arg args weight =
    if isLeftArg o args then checkArg ARight ga op arg (weight ARight)
    else if isRightArg o args then checkArg ALeft ga op arg (weight ALeft)
    else True
