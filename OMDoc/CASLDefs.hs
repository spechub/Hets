{- |
Module      :  $Header$
Description :  Hets-related functions for conversion (in\/out)
Copyright   :  (c) Hendrik Iben, Uni Bremen 2005-2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  hiben@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(Logic)

Additional definitions for interfacing CASL
-}


module OMDoc.CASLDefs
  (
  module Syntax.AS_Library,
  module Driver.Options,
  CollectionMap,
  WithOriginNode,
  IdentifierWON,
  WithOrigin (..),
  Identifier (..),
  IdNameMapping,
  findIdOpsForId,
  getLNGN,
  getIdId,
  getSensAt,
  getIdentifierAt,
  findIdIdsForId,
  findIdentifiersForId,
  compatiblePredicate,
  cv_Pred_typeToPredType,
  cv_Op_typeToOpType,
  getJustCASLSign,
  findIdPredsForId,
  inmGetLibName,
  inmGetNodeNum,
  compatibleOperator,
  getCASLSign
  )
  where

import qualified Data.Map as Map
import Syntax.AS_Library
import qualified Data.Set as Set
import qualified Data.Graph.Inductive.Graph as Graph
import qualified Common.Lib.Rel as Rel
import Common.Id
import CASL.Sign
import Static.DevGraph
import Driver.Options
import CASL.AS_Basic_CASL
import CASL.Logic_CASL
import Logic.Grothendieck
import Common.ExtSign
import Logic.Coerce

import Common.LibName (LIB_NAME)
import Data.List (partition)

-- | This datatype represents /something/ that has an origin.
data WithOrigin a b = WithOrigin { woItem::a, woOrigin::b }
-- | 'WithOrigin' specialized to 'Graph.Node' as type of origin.
type WithOriginNode a = WithOrigin a Graph.Node

-- | 'Eq' instance for 'WithOrigin'
--
-- Two 'WithOrigin'-objects are equal if their origins are equal and
-- their wrapped elements are equal.
instance (Eq a, Eq b)=>Eq (WithOrigin a b) where
  wo1 == wo2 = woOrigin wo1 == woOrigin wo2 && woItem wo1 == woItem wo2

-- | 'Ord' instance for 'WithOrigin'
--
-- 'WithOrigin'-objects are ordered by their wrapped elements unless they are
-- equal. In that case they are ordered by their origin.
instance (Eq a, Ord b, Ord a)=>Ord (WithOrigin a b) where
  compare wo1 wo2 =
    let
      icmp = compare (woItem wo1) (woItem wo2)
    in
      if icmp == EQ then compare (woOrigin wo1) (woOrigin wo2) else icmp

-- | type conversion. Ommit 'Range'
cv_Op_typeToOpType::OP_TYPE->OpType
cv_Op_typeToOpType (Op_type fk args res _) = OpType fk args res

-- | type conversion. Ommit 'Range'
cv_Pred_typeToPredType::PRED_TYPE->PredType
cv_Pred_typeToPredType (Pred_type args _) = PredType args

type CollectionMap =
  Map.Map
    (LIB_NAME, Graph.Node)
    (Map.Map LIB_NAME (Set.Set (IdentifierWON, String)))

-- | 'Identifier'S with origins
type IdentifierWON = WithOriginNode Identifier

-- | Cast Signature to CASLSignature if possible
getCASLSign :: G_sign -> Maybe CASLSign
getCASLSign (G_sign lid sign _) = do
    ExtSign caslSign _ <- coerceSign lid CASL "getCASLSign" sign
    return caslSign


-- | wrapper around (CASL) symbols
data Identifier =
    IdNodeName Id
  | IdId Id
  | IdOpM Id OpType (Maybe (Int, Id)) Bool
  | IdPred Id PredType
  | IdSens Id Int
  -- | for generated predicates ('Induction.inductionScheme')
  | IdGaPred Id PredType
  deriving Show


-- | uniform types for 'Identifier'
data IdentifierType = IdTNodeName | IdTId | IdTOpM | IdTPred | IdTSens | IdTGaPred
  deriving (Show, Eq, Ord)


-- | get type for an 'Identifier'
getIdType::Identifier->IdentifierType
getIdType (IdNodeName {}) = IdTNodeName
getIdType (IdId {}) = IdTId
getIdType (IdOpM {}) = IdTOpM
getIdType (IdPred {}) = IdTPred
getIdType (IdSens {}) = IdTSens
getIdType (IdGaPred {}) = IdTGaPred

-- | uniformly project the 'Id' an 'Identifier' refers to
getIdId::Identifier->Id
getIdId (IdNodeName i) = i
getIdId (IdId i) = i
getIdId (IdOpM i _ _ _) = i
getIdId (IdPred i _) = i
getIdId (IdSens i _) = i
getIdId (IdGaPred i _) = i


-- | equality for 'Identifier'S. Uses equality of wrapped data
-- (except for disambiguation 'Int'S)
instance Eq Identifier where
  (IdNodeName x) == (IdNodeName y) = x == y
  (IdId x) == (IdId y) = x == y
  (IdOpM x xt _ _) == (IdOpM y yt _ _) = x == y && xt == yt
  (IdPred x xt) == (IdPred y yt) = x == y && xt == yt
  (IdSens x _) == (IdSens y _) = x == y
  (IdGaPred x xt) == (IdGaPred y yt) = x == y && xt == yt
  _ == _ = False

-- | ordering for 'Identifier'S. Orders by 'IdentifierType' unless equal.
-- Orders by string representation if equal.
instance Ord Identifier where
  x `compare` y =
    if (getIdType x) == (getIdType y)
      then
        (show x) `compare`(show y)
      else
        (getIdType x) `compare` (getIdType y)



instance (Show a, Show b)=>Show (WithOrigin a b) where
  show wo = (show (woItem wo)) ++ " Origin:(" ++ (show (woOrigin wo)) ++ ")"


-- | check type compatibility for two predicates
compatiblePredicate::Rel.Rel SORT->PredType->PredType->Bool
compatiblePredicate sortrel pt1 pt2 =
  compatibleTypes sortrel (predArgs pt1) (predArgs pt2)


-- | check for type compatibility
-- a type /t1/ is compatible to a type /t2/ if
-- a) /t1 == t2/ or b) /t1/ is a subtype of /t2/
--
-- Each sort in the given lists must be /compatible/ to the sort
-- at the same position in the other list. That is, the sorts in the
-- first lists must be of the same or of a sub-type of the sort in the
-- second list.
--
-- See 'isTypeOrSubType'
compatibleTypes::
  Rel.Rel SORT
  ->[SORT] -- ^ types to compare (/given/)
  ->[SORT] -- ^ types to compare (/needed/)
  ->Bool
compatibleTypes _ [] [] = True
compatibleTypes _ [] _ = False
compatibleTypes _ _ [] = False
compatibleTypes sortrel (s1:r1) (s2:r2) =
  (isTypeOrSubType sortrel s1 s2) && (compatibleTypes sortrel r1 r2)


-- | check if a type t1 is a subtype of a type t2
--
-- Returns 'True' iff the first sort is the same as the second sort
-- or the first sort is a subsort of the second sort.
--
-- Uses 'Rel.path' /first/ /second/ /rel/ to check subsort.
isTypeOrSubType::
  Rel.Rel SORT
  ->SORT
  ->SORT
  ->Bool
isTypeOrSubType sortrel givensort neededsort =
  (givensort == neededsort)
    || (Rel.path givensort neededsort sortrel)



-- | This type is used for constructing unique names for
-- use in OMDoc-Documents.
--
-- Essential it provides a mapping for a single theory (node) but
-- these are constructed for a full library environment.
type IdNameMapping =
  (
      LIB_NAME
    , NodeName
    , String
    , Graph.Node
    , Set.Set (Id, String)
    , Set.Set ((Id, PredType), String)
    , Set.Set ((Id, OpType, Maybe (Int, Id)), String)
    , Set.Set ((Id, Int), String)
    , Set.Set ((Id, PredType), String)
  )

getSensAt
  ::CollectionMap
  ->(LIB_NAME, Graph.Node)
  ->[((IdentifierWON, Int), String)]
getSensAt
  collectionMap
  location
  =
  foldl
    (\l (i, uName) ->
      case woItem i of
        (IdSens _ snum) ->
          l ++ [((i, snum), uName)]
        _ -> l
    )
    []
    $
    getIdentifierAt collectionMap location

-- | projection function for library name
inmGetLibName::IdNameMapping->LIB_NAME
inmGetLibName (ln, _, _, _, _, _, _, _, _) = ln

-- | check type compatibility for two operators
compatibleOperator::Rel.Rel SORT->OpType->OpType->Bool
compatibleOperator sortrel ot1 ot2 =
--  (\x -> Debug.Trace.trace ("Comparing " ++ show ot1 ++ " to " ++ show ot2 ++ " -> " ++ show x) x)
--  $
  (isTypeOrSubType sortrel (opRes ot1) (opRes ot2))
  &&
  (compatibleTypes sortrel (opArgs ot1) (opArgs ot2))


-- | projection function for node (number)
inmGetNodeNum::IdNameMapping->Graph.Node
inmGetNodeNum (_, _, _, nn, _, _, _, _, _) = nn

-- | like a typed /fromMaybe/
getJustCASLSign :: Maybe CASLSign -> CASLSign
getJustCASLSign = maybe (error "getJustCASLSign") id

-- | search for a mapping where the library name and the node match the given
-- values
getLNGN::[IdNameMapping]->LIB_NAME->Graph.Node->Maybe IdNameMapping
getLNGN [] _ _ = Nothing
getLNGN (h:r) ln nn
  | (inmGetLibName h) == ln && (inmGetNodeNum h) == nn = Just h
  | otherwise = getLNGN r ln nn



-- convenience
getIdentifierAt
  ::CollectionMap
  ->(LIB_NAME, Graph.Node)
  ->[(IdentifierWON, String)]
getIdentifierAt
  collectionMap
  location
  =
  let
    locMap = Map.findWithDefault Map.empty location collectionMap
  in
    Map.fold
      (\iset il ->
        il ++ (Set.toList iset)
      )
      []
      locMap

findIdIdsForId
  ::CollectionMap
  ->(LIB_NAME, Graph.Node)
  ->Id
  ->[(LIB_NAME, (IdentifierWON, String))]
findIdIdsForId
  collectionMap
  location
  id'
  =
  let
    allValid = findIdentifiersForId collectionMap location id'
  in
    filter
      (\(_, (i, _)) ->
        case woItem i of
          (IdId {}) ->
            True
          _ ->
            False
      )
      allValid

findIdentifiersForId
  ::CollectionMap
  ->(LIB_NAME, Graph.Node)
  ->Id
  ->[(LIB_NAME, (IdentifierWON, String))]
findIdentifiersForId
  collectionMap
  location
  id'
  =
  let
    locMap = Map.findWithDefault Map.empty location collectionMap
    onlyNames =
      Map.filter
        (not . Set.null)
        $
        Map.map
          (\s ->
            Set.filter
              (\(idwo, _) ->
                getIdId (woItem idwo) == id'
              )
              s
          )
          locMap
    asList =
      concatMap
        (\(ln, s) ->
          map (\i -> (ln, i)) $ Set.toList s
        )
        $
        Map.toList
          onlyNames
  in
    asList

findIdPredsForId
  ::Rel.Rel SORT
  ->PredType
  ->CollectionMap
  ->(LIB_NAME, Graph.Node)
  ->Id
  ->[(LIB_NAME, (IdentifierWON, String))]
findIdPredsForId
  srel
  ptype
  collectionMap
  location
  id'
  =
  let
    allValid = findIdentifiersForId collectionMap location id'
    compPr =
      filter
        (\(_, (i, _)) ->
          case woItem i of
            (IdPred _ ipt) ->
              compatiblePredicate srel ipt ptype
            (IdGaPred _ ipt) ->
              compatiblePredicate srel ipt ptype
            _ ->
              False
        )
        allValid
    (eqpr, comp) =
      Data.List.partition
        (\(_, (i, _)) ->
          case woItem i of
            (IdPred _ ipt) ->
              ipt == ptype
            (IdGaPred _ ipt) ->
              ipt == ptype
            _ ->
              False
        )
        compPr
  in
    if null eqpr then comp else eqpr

findIdOpsForId
  ::Rel.Rel SORT
  ->OpType
  ->CollectionMap
  ->(LIB_NAME, Graph.Node)
  ->Id
  ->[(LIB_NAME, (IdentifierWON, String))]
findIdOpsForId
  srel
  otype
  collectionMap
  location
  id'
  =
  let
    allValid = findIdentifiersForId collectionMap location id'
    compOp =
      filter
        (\ (_, (i, _)) ->
          case woItem i of
            (IdOpM _ iot _ _) ->
              compatibleOperator srel iot otype
            _ ->
              False
        )
        allValid
    (eqop, comp) =
      Data.List.partition
        (\ (_, (i, _)) ->
          case woItem i of
            (IdOpM _ iot _ _) ->
              iot { opKind = opKind otype } == otype
            _ -> False
        )
        compOp
  in
    if null eqop then comp else eqop

