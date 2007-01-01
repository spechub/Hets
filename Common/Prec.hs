{- |
Module      :  $Header$
Description :  precedence checking
Copyright   :  Christian Maeder and Uni Bremen 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable

Precedence checking
-}

module Common.Prec where

import Common.Id
import Common.GlobalAnnotations
import Common.AS_Annotation
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel

-- | a precedence map using numbers for faster lookup
data PrecMap = PrecMap
    { precMap :: Map.Map Id Int
    , relWeight :: Int
    , maxWeight :: Int
    } deriving Show

emptyPrecMap :: PrecMap
emptyPrecMap = PrecMap
    { precMap = Map.empty
    , relWeight = 0
    , maxWeight = maxBound
    }

mkPrecIntMap :: Rel.Rel Id -> PrecMap
mkPrecIntMap r =
    let (m, t) = Rel.toPrecMap r
        in emptyPrecMap
               { precMap = m
               , relWeight = Map.findWithDefault (div t 2) eqId m
               , maxWeight = t
               }

getIdPrec :: PrecMap -> Set.Set Id -> Id -> Int
getIdPrec p ps i = let m = maxWeight p in
    if i == applId then m + 1
    else Map.findWithDefault
    (if begPlace i || endPlace i then
         if Set.member i ps then relWeight p else m
     else m + 2) i $ precMap p

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
    in if argPrec <= 0 then False
       else case compare argPrec opPrec of
           LT -> False
           GT -> True
           EQ -> if joinPlace side arg then
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
