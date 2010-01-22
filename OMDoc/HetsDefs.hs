{- |
Module      :  $Header$
Description :  Hets-related functions for conversion (in\/out)
Copyright   :  (c) Hendrik Iben, Uni Bremen 2005-2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  hiben@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(Logic)

Additional definitions for interfacing Hets
-}
module OMDoc.HetsDefs
    ( dho
    , getFlatNames
    , getMultiOrigins
    , findMultiOriginUnifications
    , traceRealIdentifierOrigins
    , identifyFlatNames
    , removeReferencedIdentifiers
    , getIdUseNumber
    , makeUniqueNames
    , makeCollectionMap
    , makeUniqueIdNameMapping
    , isDefLinkType
    , isDefLink
    , SentenceWO
    , WithOrigin (..)
    , Identifier (..)
    , getIdId
    , CollectionMap
    , IdentifierWON
    , WithOriginNode
    , idToString
    , NodeNameWO
    , SORTWO
    , getNameForSens
    , IdNameMapping
    , inmGetNodeNum
    , inmGetLibName
    , inmGetIdNameSortSet
    , inmGetIdNameOpSet
    , inmGetIdNameConstructors
    , inmGetIdNamePredSet
    , inmGetIdNameGaPredSet
    , inmGetNodeId
    , inmGetNodeName
    , inmGetIdNameAllSet
    , inmFindLNNN
    , isEmptyMorphism
    , getNameForPred
    , getNameForSort
    , getNameForOp
    , getNameOrigin
    , getNodeSentences
    , nodeNameToId
    , findOriginInCurrentLib
    , findIdentifiersForName
    , findIdIdsForName
    , findIdPredsForName
    , findIdOpsForName
    , findIdentifiersForId
    , findIdIdsForId
    , findIdPredsForId
    , findIdOpsForId
    , getIdentifierAt
    , getSortsAt
    , getPredsAt
    , getOpsAt
    , getSensAt
    , getDefinedIdentifierAt
    , getDefinedSortsAt
    , getDefinedPredsAt
    , getDefinedOpsAt
    , getDefinedSensAt
    , getCASLMorphLL
    , getJustCASLSign
    , getCASLSign
    , cv_Op_typeToOpType
    , cv_Pred_typeToPredType
    , getLNGN
    , compatiblePredicate
    , compatibleOperator
    -- used by input --
    , cv_OpTypeToOp_type
    , cv_PredTypeToPred_type
    , mkWON
    , isEmptyHidAndReqL
    , isNonHidingHidAndReqL
    , emptyCASLMorphism
    , emptyCASLGMorphism
    , emptyCASLSign
    , RequationList
    , HidingAndRequationList
    , makeCASLGMorphism
    , Imports
    , ImportsMap
    -- unused but may be used
    , getNameOrigins
    , getIdOrigins
    , idToNodeName
    , wonOrigin
  )
  where

import CASL.AS_Basic_CASL
import CASL.Logic_CASL
import CASL.Morphism
import CASL.Sign

import Common.ExtSign
import Common.Id
import Common.LibName
import Common.Utils (trim)

import Data.List (find, nub, partition, intercalate)

import Debug.Trace (trace)

import Driver.Options

import Logic.Coerce
import Logic.Comorphism
import Logic.Grothendieck

import OMDoc.Util

import Static.DevGraph
import Static.GTheory

import qualified CASL.Induction as Induction

import qualified Common.AS_Annotation as Ann
import qualified Common.Lib.Rel as Rel
import qualified Common.Result as Result

import qualified Data.Graph.Inductive.Graph as Graph
import qualified Data.Map as Map
import qualified Data.Set as Set

import qualified Logic.Prover as Prover

-- | \"alias\" for 'defaultHetcatsOpts' (for export)
dho::HetcatsOpts
dho = defaultHetcatsOpts

-- | Cast Signature to CASLSignature if possible
getCASLSign :: G_sign -> Maybe CASLSign
getCASLSign (G_sign lid sign _) = do
    ExtSign caslSign _ <- coerceSign lid CASL "getCASLSign" sign
    return caslSign

-- | like a typed /fromMaybe/
getJustCASLSign :: Maybe CASLSign -> CASLSign
getJustCASLSign = maybe (error "getJustCASLSign") id

-- | extract a 'CASL.Morphism.Morphism' from a 'DGLinkLab'
-- will fail if not possible
getCASLMorphLL::DGLinkLab->(CASL.Morphism.Morphism () () ())
getCASLMorphLL edge =
  maybe (error "cannot cast morphism to CASL.Morphism") id $ do
    Logic.Grothendieck.GMorphism cid _ _ morph _ <- return $ dgl_morphism edge
    coerceMorphism (targetLogic cid) CASL "getCASLMorphLL" morph

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

instance (Show a, Show b)=>Show (WithOrigin a b) where
  show wo = (show (woItem wo)) ++ " Origin:(" ++ (show (woOrigin wo)) ++ ")"

-- | extract wrapped element from 'WithOrigin'
wonItem::WithOriginNode a->a
wonItem = woItem

-- | extract origin from 'WithOrigin'
wonOrigin::WithOriginNode a->Graph.Node
wonOrigin = woOrigin

-- | create an element with origin where the origin is a 'Graph.Node'
mkWON::a->Graph.Node->WithOriginNode a
mkWON = WithOrigin


-- | get CASL-formulas from a node
getNodeSentences::DGNodeLab->[Ann.Named CASLFORMULA]
getNodeSentences node = if isDGRef node then [] else
  maybe (error "getNodeSentences") id $ do
    G_theory lid _ _ thsens _ <- return $ dgn_theory node
    coerceSens lid CASL "getNodeSentences" $ Prover.toNamedList thsens

-- | create a mapping over all nodes of a DevGraph
-- where a checker function is provided to filter out
-- unwanted results
getNodeDGNameMappingWO::
  DGraph -- ^ DevGraph to use
  ->(DGraph->Graph.Node->a) -- ^ mapping function
  ->(a->Bool) -- ^ checker function, to determine of the
              -- result of the mapping function is to be kept
  ->(Map.Map NodeNameWO a)
getNodeDGNameMappingWO dg mapper dispose =
   foldl (\mapping (n,node) ->
    let mapped = mapper dg n
    in
    if dispose mapped then
      mapping
    else
      Map.insert (mkWON (dgn_name node) n) mapped mapping
    ) Map.empty $ labNodesDG dg


-- added Integer to keep the order of imports (to OMDoc, from OMDoc)
-- | abstract imports
type Imports = Set.Set (Int, (String, HidingAndRequationList, Bool))

-- | node names with origin (node number)
type NodeNameWO = WithOriginNode NodeName

-- | sorts with origin
type SORTWO = WithOriginNode SORT

-- | 'Id'S with origin
type IdWO = WithOriginNode Id

-- | 'Ann.Named' 'CASLFORMULA'S with origin
type SentenceWO = WithOriginNode (Ann.Named CASLFORMULA)

-- | set of 'SORTWO'S
type SortsWO = Set.Set SORTWO

-- | map of predicate ids with origin to
-- their set of types
type PredsWO = Map.Map IdWO (Set.Set PredType)

-- | map of operator ids with origin to
-- their set of types
type OpsWO = Map.Map IdWO (Set.Set OpType)

-- | map of 'Imports' (for theories)
type ImportsMap = Map.Map String Imports

-- | map of node names with origin to their sorts with origin
type SortsMapDGWO = Map.Map NodeNameWO SortsWO

-- | map of node names with origin to their predicates with origin
type PredsMapDGWO = Map.Map NodeNameWO PredsWO

-- | map of node names with origin to their operators with origin
type OpsMapDGWO = Map.Map NodeNameWO OpsWO

-- | Emptyness test for morphisms.
--
-- Tests for emptyness of sort- function- and predicate-map.
isEmptyMorphism:: Morphism a b c ->Bool
isEmptyMorphism m =
  Map.null (sort_map m) && Map.null (op_map m) && Map.null (pred_map m)

-- | returns an empty 'CASL.Morphism.Morphism'
emptyCASLMorphism:: CASL.Morphism.Morphism () () ()
emptyCASLMorphism =
    CASL.Morphism.embedMorphism () (emptySign ()) (emptySign ())

-- | returns an empty 'Logic.Grothendieck.GMorphism' with an internal 'emptyCASLMorphism'
emptyCASLGMorphism::Logic.Grothendieck.GMorphism
emptyCASLGMorphism = Logic.Grothendieck.gEmbed $
    Logic.Grothendieck.mkG_morphism CASL emptyCASLMorphism

-- | injects a 'CASL.Morphism.Morphism' into a 'Logic.Grothendieck.GMorphism'
makeCASLGMorphism :: CASL.Morphism.Morphism () () ()
                  -> Logic.Grothendieck.GMorphism
makeCASLGMorphism m = Logic.Grothendieck.gEmbed $
    Logic.Grothendieck.mkG_morphism CASL m

-- | return an empty 'CASLSign'
emptyCASLSign::CASLSign
emptyCASLSign = emptySign ()

-- | abstract symbol requations (theory, name) -> (theory, name)
type RequationList = [ ( (String, String), (String, String) ) ]

-- | abstract symbol requations and a list of hidden symbols
type HidingAndRequationList = ([String], RequationList)

-- | test if there are no requations (but maybe hiding)
isEmptyHidAndReqL::HidingAndRequationList->Bool
isEmptyHidAndReqL (_, l) = null l

-- | test if there is no hiding (but maybe requations)
isNonHidingHidAndReqL::HidingAndRequationList->Bool
isNonHidingHidAndReqL (h, _) = null h


-- | Instance of 'Read' for 'Id'S
instance Read Id where
  readsPrec _ ('[':s) =
    let
      (tokens, rest) = spanEsc (not . (flip elem "[]")) s
      tokenl = breakIfNonEsc "," tokens
      token = map (\str -> Token (trim $ unesc str) nullRange) tokenl
      idl = breakIfNonEsc "," rest
      ids = foldl (\ids' str ->
        case ((readsPrec 0 (trim str))::[(Id, String)]) of
          [] -> error ("Unable to parse \"" ++ str ++ "\"")
          ((newid,_):_) -> ids' ++ [newid]
          ) [] idl
    in
      case (trim rest) of
        (']':_) -> [(Id token [] nullRange, "")]
        _ -> [(Id token ids nullRange, "")]

  readsPrec _ _ = []

-- | escapes special characters. used in 'idToString'.
escapeForId::String->String
escapeForId [] = []
escapeForId ('\\':r) = "\\\\" ++ escapeForId r
escapeForId ('[':r) = "\\[" ++ escapeForId r
escapeForId (']':r) = "\\]" ++ escapeForId r
escapeForId (',':r) = "\\," ++ escapeForId r
escapeForId (' ':r) = "\\ " ++ escapeForId r
escapeForId (c:r) = c:escapeForId r

-- | creates a parseable representation of an 'Id' (see Read-instance)
idToString::Id->String
idToString (Id toks ids _) =
                "[" ++
                (intercalate "," (map (\t -> escapeForId $ tokStr t) toks)) ++
                (intercalate "," (map idToString ids)) ++
                "]"

-- | encapsulates a node_name in an id
nodeNameToId::NodeName->Id
nodeNameToId (NodeName s e n _) =
  mkId [s, mkSimpleId e, mkSimpleId (show n)]

-- | reads back an encapsulated node_name
idToNodeName::Id->NodeName
idToNodeName (Id toks _ _) = case toks of
  t0 : t1 : t2 : _ -> NodeName t0 (show t1) (read $ show t2) []
  _ -> error "idToNodeName"

-- | This type is used for constructing unique names for
-- use in OMDoc-Documents.
--
-- Essential it provides a mapping for a single theory (node) but
-- these are constructed for a full library environment.
type IdNameMapping =
  (
      LibName
    , NodeName
    , String
    , Graph.Node
    , Set.Set (Id, String)
    , Set.Set ((Id, PredType), String)
    , Set.Set ((Id, OpType, Maybe (Int, Id)), String)
    , Set.Set ((Id, Int), String)
    , Set.Set ((Id, PredType), String)
  )


{-
instance Show IdNameMapping where
  show (ln, nn, nsn, nnum, sorts, preds, ops, sens, cons) =
    "(" ++ show ln ++ ", " ++ show nn ++ ", " ++ show nsn ++ ", "
      ++ show nnum ++ ", " ++ show sorts ++ ", " ++ show preds ++ ", "
      ++ show ops ++ ", " ++ show sens ++ ", " ++ show cons ++ ")"
-}

-- | projection function for library name
inmGetLibName::IdNameMapping->LibName
inmGetLibName (ln, _, _, _, _, _, _, _, _) = ln

-- | projection function for node name
inmGetNodeName::IdNameMapping->NodeName
inmGetNodeName (_, nn, _, _, _, _, _, _, _) = nn

-- | projection function for XML node name (theory name)
inmGetNodeId::IdNameMapping->String
inmGetNodeId (_, _, id', _, _, _, _, _, _) = id'

-- | projection function for node (number)
inmGetNodeNum::IdNameMapping->Graph.Node
inmGetNodeNum (_, _, _, nn, _, _, _, _, _) = nn

-- | projection function for the set of sorts
inmGetIdNameSortSet::IdNameMapping->Set.Set (Id, String)
inmGetIdNameSortSet (_, _, _, _, s, _, _, _, _) = s

-- | projection function for the disambiguated set of predicates
inmGetIdNamePredSet::IdNameMapping->Set.Set ((Id, PredType), String)
inmGetIdNamePredSet (_, _, _, _, _, s, _, _, _) = s

-- | projection function for the disambiguated set of operators
inmGetIdNameOpSet::IdNameMapping->Set.Set ((Id, OpType), String)
inmGetIdNameOpSet (_, _, _, _, _, _, s, _, _) = Set.map (\((i, t, _), u) -> ((i, t), u)) s

-- | projection function for the sentences (annotated by their appearance)
inmGetIdNameSensSet::IdNameMapping->Set.Set ((Id, Int), String)
inmGetIdNameSensSet (_, _, _, _, _, _, _, s, _) = s

-- | projection function for the operators that represent constructors
inmGetIdNameConstructors::IdNameMapping->Set.Set ((Id, OpType, Int, Id), String)
inmGetIdNameConstructors (_, _, _, _, _, _, s, _, _) =
  Set.fold
    (\((i, t, m), u) newset ->
      case m of
        Nothing ->
          newset
        (Just (n, a)) ->
          Set.insert ((i, t, n, a), u) newset
    )
    Set.empty
    s

-- | projection function for the predicates generated by 'Induction.inductionScheme'
inmGetIdNameGaPredSet::IdNameMapping->Set.Set ((Id, PredType), String)
inmGetIdNameGaPredSet (_, _, _, _, _, _, _, _, s) = s

-- | get just a set with all known 'Id'S and their XML-names
-- ('Id'S can show up more than once because their XML-name differs).
--
-- This does not contain the 'Id's from 'inmGetIdNameGaPredSet'.
inmGetIdNameAllSet::IdNameMapping->Set.Set (Id, String)
inmGetIdNameAllSet inm =
  Set.union
    (
      Set.union
        (inmGetIdNameSortSet inm)
        (
          Set.map
            (\( (id', _), s') -> (id', s'))
            (inmGetIdNameSensSet inm)
        )
    )
    (
      Set.union
        (
        Set.map
          (\( (id',_), s') -> (id', s'))
          (inmGetIdNamePredSet inm)
        )
        (
        Set.map
          (\( (id',_), s') -> (id', s'))
          (inmGetIdNameOpSet inm)
        )
    )

-- | projection function to get library name and node number
inmGetLNNN::IdNameMapping->(LibName, Graph.Node)
inmGetLNNN inm = (inmGetLibName inm, inmGetNodeNum inm)

-- | searches for mapping where library name and node number match
inmFindLNNN::(LibName, Graph.Node)->[IdNameMapping]->Maybe IdNameMapping
inmFindLNNN lnnn = find (\inm -> inmGetLNNN inm == lnnn)

-- | filter a list of mappings to keep only mappings that contain a
-- given 'Id'
getIdOrigins::[IdNameMapping]->Id->[IdNameMapping]
getIdOrigins [] _ = []
getIdOrigins (o:r) sid =
  (
    if
      Set.null
        $
        Set.filter
          (\(sid', _) -> sid' == sid)
          $
          inmGetIdNameAllSet o
      then
        []
      else
        [o]
  ) ++ getIdOrigins r sid

-- | like 'getIdOrigins' but search for an XML-name instead of an 'Id'
getNameOrigins::[IdNameMapping]->String->[IdNameMapping]
getNameOrigins [] _ = []
getNameOrigins (o:r) name =
  (
    if
      Set.null
        $
        Set.filter
          (\(_, name') -> name' == name)
          $
          inmGetIdNameAllSet o
      then
        []
      else
        [o]
  ) ++ getNameOrigins r name

-- | check whether a list of mappings contains a mapping for a given
-- library and node number and if this mappings contains entries for
-- a given XML-name.
--
--Returns the empty list, if there is no such mapping. Otherwise a list with
--one element is returned.
getNameOrigin::[IdNameMapping]->LibName->Graph.Node->String->[IdNameMapping]
getNameOrigin names ln node name =
  case getLNGN names ln node of
    Nothing -> []
    (Just o) ->
      if
        Set.null
          $
          Set.filter
            (\(_, name') -> name' == name)
            $
            inmGetIdNameAllSet o
      then
        []
      else
        [o]


-- | search for a mapping where the library name and the node match the given
-- values
getLNGN::[IdNameMapping]->LibName->Graph.Node->Maybe IdNameMapping
getLNGN [] _ _ = Nothing
getLNGN (h:r) ln nn
  | (inmGetLibName h) == ln && (inmGetNodeNum h) == nn = Just h
  | otherwise = getLNGN r ln nn

-- | go through a list of mappings, extract part of the mapping, process that
-- part and check if this processed part is what is searched for. If yes,
-- transform into a name ('String').
--
-- Stops at first match.
getNameFor::
  [IdNameMapping] -- ^ list to search in
  ->(IdNameMapping->a) -- ^ part extractor
  ->(a->c) -- ^ part processor
  ->(c->Bool) -- ^ part checker
  ->(c->String) -- ^ applied to processed part iff checker is 'True'
  ->Maybe String
getNameFor [] _ _ _ _ = Nothing
getNameFor (h:r) translate process found extract =
  let
    processed = process $ translate h
  in
    if found processed
      then
        Just (extract processed)
      else
        getNameFor r translate process found extract

-- | search in a list of mappings for the XML-name of a given sort
getNameForSort::[IdNameMapping]->SORT->Maybe String
getNameForSort mapping s =
  getNameFor
    mapping
    inmGetIdNameSortSet
    (Set.filter (\(sid, _) -> sid == s))
    (not . Set.null)
    (snd . head . Set.toList)

-- | search in a list of mappings for the XML-name of a given predicate
-- (and type)
getNameForPred::[IdNameMapping]->(Id, PredType)->Maybe String
getNameForPred mapping (pid, pt) =
  getNameFor
    mapping
    (\nm ->
      Set.union
        (inmGetIdNameGaPredSet nm)
        (inmGetIdNamePredSet nm)
    )
    (Set.filter (\((pid', pt'), _) -> pid' == pid && pt' == pt))
    (not . Set.null)
    (snd . head . Set.toList)

-- | search in a list of mappings for the XML-name of a fiven operator
-- (and type)
getNameForOp::[IdNameMapping]->(Id, OpType)->Maybe String
getNameForOp mapping (oid, ot) =
  getNameFor
    mapping
    inmGetIdNameOpSet
    (Set.filter (\((oid', ot'), _) -> oid' == oid && ot' == ot))
    (not . Set.null)
    (snd . head . Set.toList)

-- | search in a list of mappings for the XML-name of a given
-- sentence name (and apperance-tag)
getNameForSens::[IdNameMapping]->(Id, Int)->Maybe String
getNameForSens mapping (s,sn) =
  getNameFor
    mapping
    inmGetIdNameSensSet
    (Set.filter (\((sid, sn'), _) -> sid == s && sn' == sn))
    (not . Set.null)
    (snd . head . Set.toList)

-- | type conversion. Ommit 'Range'
cv_Op_typeToOpType::OP_TYPE->OpType
cv_Op_typeToOpType (Op_type fk args res _) = OpType fk args res

-- | type conversion. Set range to 'nullRange'.
cv_OpTypeToOp_type::OpType->OP_TYPE
cv_OpTypeToOp_type (OpType fk args res) = Op_type fk args res nullRange

-- | type conversion. Ommit 'Range'
cv_Pred_typeToPredType::PRED_TYPE->PredType
cv_Pred_typeToPredType (Pred_type args _) = PredType args

-- | type conversion. Set range to 'nullRange'.
cv_PredTypeToPred_type::PredType->PRED_TYPE
cv_PredTypeToPred_type (PredType args) = Pred_type args nullRange

-- | translate a named 'CASLFORMULA' into a set of operators
-- corresponding to the /Sort_gen_ax/-axiom.
--
-- Anything else than a /Sort_gen_ax/-axiom for input results in an
-- empty set.
extractConstructorOps::Ann.Named CASLFORMULA->Set.Set (Id, OpType)
extractConstructorOps ansen =
  case Ann.sentence ansen of
    (Sort_gen_ax cons _) ->
      foldl
        (\ops (Constraint _ symbs _) ->
          foldl
            (\ops' (Qual_op_name name ot _) ->
              Set.insert (name, cv_Op_typeToOpType ot) ops'
            )
            ops
            (map fst symbs)
        )
        Set.empty
        cons
    _ -> Set.empty


-- | translate a node name to a string like 'showName' but
-- creates the strign \"/AnonNode/\" if the node name is empty
nodeNameToName::NodeName->String
nodeNameToName =
  (\nn ->
    let
      nodename = showName nn
    in
      if (length nodename) == 0
        then
          "AnonNode"
        else
          nodename
  )

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

-- | 'Identifier'S with origins
type IdentifierWON = WithOriginNode Identifier

-- | extract predicates from 'FORMULA'S.
--
-- Applied recursively to all internal 'FORMULA'S. Internal
-- 'TERM'S are processed by 'getRecursivePredicatesT'.
getRecursivePredicates::FORMULA f->[PRED_SYMB]
getRecursivePredicates (Quantification _ _ f _) =
  getRecursivePredicates f
getRecursivePredicates (Conjunction fs _) =
  concatMap getRecursivePredicates fs
getRecursivePredicates (Disjunction fs _) =
  concatMap getRecursivePredicates fs
getRecursivePredicates (Implication f1 f2 _ _) =
  (getRecursivePredicates f1) ++ (getRecursivePredicates f2)
getRecursivePredicates (Equivalence f1 f2 _) =
  (getRecursivePredicates f1) ++ (getRecursivePredicates f2)
getRecursivePredicates (Negation f _) =
  getRecursivePredicates f
getRecursivePredicates (Predication ps t _) =
  [ps] ++ (concatMap getRecursivePredicatesT t)
getRecursivePredicates (Definedness t _) =
  getRecursivePredicatesT t
getRecursivePredicates (Existl_equation t1 t2 _) =
  (getRecursivePredicatesT t1) ++ (getRecursivePredicatesT t2)
getRecursivePredicates (Strong_equation t1 t2 _) =
  (getRecursivePredicatesT t1) ++ (getRecursivePredicatesT t2)
getRecursivePredicates (Membership t _ _) =
  getRecursivePredicatesT t
getRecursivePredicates _ =
  []

-- | extract predicates from 'TERM'S.
--
-- Applied recursively to all internal 'TERM'S. Internal
-- 'FORMULA'S are processed by 'getRecursivePredicates'.
getRecursivePredicatesT::TERM f->[PRED_SYMB]
getRecursivePredicatesT (Application _ ts _) =
  concatMap getRecursivePredicatesT ts
getRecursivePredicatesT (Sorted_term t _ _) =
  getRecursivePredicatesT t
getRecursivePredicatesT (Cast t _ _) =
  getRecursivePredicatesT t
getRecursivePredicatesT (Conditional t1 f t2 _) =
  (getRecursivePredicatesT t1)
  ++
  (getRecursivePredicates f)
  ++
  (getRecursivePredicatesT t2)
getRecursivePredicatesT _ =
  []


hasOperator
  ::OpsMapDGWO
  ->NodeNameWO
  ->Id
  ->OpType
  ->Bool
hasOperator
  opsmapdgwo
  nnwo
  opid
  optype
  =
  let
    opsMap = Map.findWithDefault Map.empty nnwo opsmapdgwo
    withId =
      Map.foldWithKey
        (\idwo os wI ->
          if woItem idwo == opid
            then
              if Set.member optype os
                then
                  Map.insertWith Set.union idwo (Set.singleton optype) wI
                else
                  wI
            else
              wI
        )
        Map.empty
        opsMap
  in
    not $ Map.null withId

-- | Collect all used symbols from a library environment.
--
-- Inspects all signatures and sentences and collects generated predicates
-- by extracting them with 'getRecursivePredicates' from the corresponding
-- axioms.
--
-- Uses 'createNODENAMEWOMap' and 'extractConstructorOps'.
getFlatNames::LibEnv->Map.Map LibName (Set.Set IdentifierWON)
getFlatNames lenv =
  foldl
    (\fm ln ->
      let
        dg = lookupDGraph ln lenv
        -- extract sorts, predicates and operators
        (sortswomap, predswomap, opswomap) =
          separateIdentifiers
            $
            createNODENAMEWOMap dg
        dgnodes = filter (not . isDGRef . snd) $ labNodesDG dg
        -- collected node names
        nodenameids =
          map
            (\(nn, node) -> (nn, stringToId $ nodeNameToName $ dgn_name node))
            dgnodes
        -- collect and label sentences
        senslist =
          concatMap
            (\(nn, node) -> map (\x -> (nn, x)) $ zip [(1 :: Int) ..]
                            (getNodeSentences node))
            dgnodes
        -- get constructors from sentences
        senscons =
          concatMap
            (\(nodenum, (sennum, s)) ->
              Set.toList
                $
                Set.map
                  (\(cid, ot) -> (nodenum, (sennum, cid, ot)))
                  (extractConstructorOps s)
            )
            senslist
        -- find sort generating predicates
        sortgenpreds =
          Map.insertWith
            Set.union
            ln
            (
              Set.fromList
                $
                nub
                  $
                  foldl
                    (\sgp (nn, (_, s)) ->
                      case Ann.sentence s of
                        (Sort_gen_ax constraints _) ->
                          let
                            soCon = Induction.inductionScheme constraints
                            ps =
                              case Result.resultToMaybe soCon of
                                Nothing ->
                                  []
                                Just cf ->
                                  getRecursivePredicates (cf :: FORMULA ())
                            sennode = labDG dg nn
                            nnamewo = mkWON (dgn_name sennode) nn
                            constraintsOps =
                              concatMap
                                (\(Constraint _ cops _ ) ->
                                  foldl
                                    (\cl (cop, _) ->
                                      case cop of
                                        (Qual_op_name copid coptype _) ->
                                          case
                                            filter
                                              (\(_, (_, cid, cot)) ->
                                                cid == copid
                                                && cot == cv_Op_typeToOpType coptype
                                              )
                                              senscons
                                          of
                                            [] ->
                                              if
                                                hasOperator
                                                  opswomap
                                                  nnamewo
                                                  copid
                                                  (cv_Op_typeToOpType coptype)
                                                then
                                                  cl
                                                else
                                                  cl ++
                                                  [
                                                    mkWON
                                                      (
                                                        IdOpM
                                                          copid
                                                          (cv_Op_typeToOpType coptype)
                                                          Nothing
                                                          True
                                                      )
                                                      nn
                                                  ]
                                            _ ->
                                              cl
                                        _ ->
                                          error "Unqualified OpName in Constraints!"
                                    )
                                    []
                                    cops
                                )
                                constraints
                          in
                            sgp
                            ++
                            (
                              map
                                (\psym ->
                                  case psym of
                                    (Pred_name pn) ->
                                      mkWON (IdGaPred pn (PredType [])) nn
                                    (Qual_pred_name pn pt _) ->
                                      mkWON
                                        (IdGaPred pn (cv_Pred_typeToPredType pt))
                                        nn
                                )
                                ps
                            )
                            ++
                            constraintsOps
                        _ ->
                          sgp
                    )
                    []
                    senslist
            )
            fm
        -- process sorts
        sorts' = foldl
          (\fm' sortsetwo ->
            Map.insertWith
              Set.union
              ln
              (Set.map (\swo -> mkWON (IdId (woItem swo)) (woOrigin swo) ) sortsetwo)
              fm'
          )
          sortgenpreds
          (Map.elems sortswomap)
        -- process operators
        ops' =
          foldl
            (\fm' opmapwo ->
              foldl
                (\fm'' (oid, ots) ->
                  foldl
                    (\fm''' ot ->
                      case
                        filter
                          (\(num, (_, cid, cot)) ->
                            (num == woOrigin oid) && (cid == woItem oid) && (cot == ot)
                          )
                          senscons
                      of
                        [] ->
                          Map.insertWith
                            Set.union
                            ln
                            (Set.singleton (mkWON (IdOpM (woItem oid) ot Nothing False) (woOrigin oid)))
                            fm'''
                        (_, (sennum, _, _)):_ ->
                          Map.insertWith
                            Set.union
                            ln
                            (
                              Set.singleton
                                (
                                  mkWON
                                    (
                                      IdOpM
                                        (woItem oid)
                                        ot
                                        (Just (sennum, opRes ot))
                                        False
                                    )
                                    (woOrigin oid)
                                )
                            )
                            fm'''
                    )
                    fm''
                    (Set.toList ots)
                )
                fm'
                (Map.toList opmapwo)
            )
            sorts'
            (Map.elems opswomap)
        -- process predicates
        preds' =
          foldl
            (\fm' predmapwo ->
              foldl
                (\fm'' (pid, pts) ->
                  foldl
                    (\fm''' pt ->
                      Map.insertWith
                        Set.union
                        ln
                        (Set.singleton (mkWON (IdPred (woItem pid) pt) (woOrigin pid)))
                        fm'''
                    )
                    fm''
                    (Set.toList pts)
                )
                fm'
                (Map.toList predmapwo)
            )
            ops'
            (Map.elems predswomap)
        -- process sentences
        sens' =
          foldl
            (\fm' (nodenum, (sennum, namedsen)) ->
              Map.insertWith
                Set.union
                ln
                (Set.singleton (mkWON (IdSens (stringToId $ Ann.senAttr namedsen) sennum) nodenum))
                fm'
            )
            preds'
            senslist
        -- process constructors
        -- this will override some of
        -- the previous operators
        -- but catches also sentence-related cons
        cons' =
          foldl
            (\fm' (nodenum, (sennum, cid, cot)) ->
              let
                sennode = labDG dg nodenum
                nnamewo = mkWON (dgn_name sennode) nodenum
              in
                if
                  hasOperator
                    opswomap
                    nnamewo
                    cid
                    cot
                  then
                    fm'
                  else
                  {-
                    trace
                      (
                        "Generating Constructor from Sentence: "
                        ++ (show (nodenum, (cid, cot)))
                      )
                      $
                  -}
                      Map.insertWith
                        Set.union
                        ln
                        (Set.singleton (mkWON (IdOpM cid cot (Just (sennum, opRes cot)) True) nodenum))
                        fm'
            )
            sens'
            senscons
        -- process node names
        nodes' =
          Map.insertWith
            Set.union
            ln
            (
              Set.fromList
                (
                  map
                    (\(nn, nnid)-> mkWON (IdNodeName nnid) nn)
                    nodenameids
                )
            )
            cons'
      in
        nodes'
    )
    Map.empty
    (Map.keys lenv)


-- | find out, which used symbols are actually from
-- somewhere else (imported)
identifyFlatNames::
  LibEnv
  ->Map.Map LibName (Set.Set IdentifierWON)
  ->Map.Map (LibName, IdentifierWON) (LibName, IdentifierWON)
identifyFlatNames
  lenv
  flatmap =
  let
    -- create a list of referenced (external) libraries
    reflist =
      foldl
        (\rl ln ->
          let
            dg = lookupDGraph ln lenv
            refnodes =
              filter
                (\(_, node) -> isDGRef node)
                (labNodesDG dg)
          in
            rl ++ (map (\(rnn, rnode) -> (ln, rnn, dgn_libname rnode, dgn_node rnode)) refnodes)
        )
        []
        (Map.keys lenv)
  in
    -- cure some recursive evil...
    fixIdentMap
      $
      foldl
        -- for each reference...
        (\im (refln, refnn, refedln, refednode) ->
          let
            -- identifiers for reference
            reflnids = Map.findWithDefault Set.empty refln flatmap
            -- identifiers there with origin in current library
            refedids = Set.filter (\ws -> woOrigin ws == refnn) reflnids
            -- identifiers in the referenced library
            refedlnids = Map.findWithDefault Set.empty refedln flatmap
          in
            Set.fold
              -- for each referenced identifier
              (\rws im' ->
                case
                  -- try to find at least one matching identifier in reference
                  Set.toList
                    $
                    Set.filter (\x -> woItem x == woItem rws) refedlnids
                of
                  -- if none, something is wrong (should not happen)
                  [] ->
                    {-
                    trace
                      ("The impossible : " ++ (show $ woItem rws))
                      $
                    -}
                      Map.insert (refln, rws) (refedln, mkWON (IdId $ stringToId "unknown") refednode) im'
                  -- use first matching element to construct reference information
                  -- this is correct for Hets (same name -> same thing)
                  -- but for OMDoc this equality needs to be constructed... (TODO)
                  ws:_ -> Map.insert (refln, rws) (refedln, ws) im'
              )
              im
              refedids
        )
        Map.empty
        reflist

{-
sameConAsOp::Identifier->Identifier->Bool
sameConAsOp (IdCons cid cot _) (IdOp oid oot) = cid == oid && cot == oot
sameConAsOp (IdOp oid oot) (IdCons cid cot _) = cid == oid && cot == oot
sameConAsOp i1 i2 = i1 == i2
-}

-- | find recursive identity matches and reduce targets to real identity.
--
-- Background: import from identifiers that where already imported from
-- somewhere else are not found at first.
fixIdentMap::
    Map.Map (LibName, IdentifierWON) (LibName, IdentifierWON)
  ->Map.Map (LibName, IdentifierWON) (LibName, IdentifierWON)
fixIdentMap identMap =
  Map.foldWithKey
    (\key value m ->
      let
        value' =
          case finalRecursiveTarget identMap key of
            Nothing -> value
            (Just v) -> v
      in
        Map.insert key value' m
    )
    Map.empty
    identMap

  where
    finalRecursiveTarget::(Eq a, Ord a)=>Map.Map a a->a->Maybe a
    finalRecursiveTarget m a =
      case Map.lookup a m of
        Nothing -> Nothing
        (Just a') ->
          case finalRecursiveTarget m a' of
            Nothing -> Just a'
            (Just a'') -> Just a''

findMultiOriginUnifications::
  LibEnv
  ->Map.Map LibName (Set.Set (Set.Set IdentifierWON))
  ->Map.Map (LibName, Set.Set IdentifierWON) (LibName, IdentifierWON)
findMultiOriginUnifications
  lenv
  multimap
  =
    let
      flatted =
        Map.map (\s -> Set.fromList (concatMap Set.toList (Set.toList s))) multimap
      idents = identifyFlatNames lenv flatted
      targetMap =
        Map.foldWithKey
          (\ln setofsets tM ->
            Set.fold
              (\origins tM' ->
                Set.fold
                  (\o tM'' ->
                    let
                      mt = Map.lookup (ln, o) idents
                    in
                      case mt of
                        (Just t) ->
                          Map.insertWith Set.union t (Set.singleton (ln, o)) tM''
                        _ ->
                          tM''
                  )
                  tM'
                  origins
              )
              tM
              setofsets
          )
          Map.empty
          multimap
      libgroups =
        Map.map
          (\s ->
            let
              lnMap =
                Set.fold
                  (\(oln, oi) lM ->
                    Map.insertWith Set.union oln (Set.singleton oi) lM
                  )
                  Map.empty
                  s
            in
              lnMap
          )
          targetMap
      rearranged =
        Map.foldWithKey
          (\lgTt lgM rM ->
            foldl
              (\rM' group ->
                Map.insert group lgTt rM'
              )
              rM
              (Map.toList lgM)
          )
          Map.empty
          libgroups
    in
      rearranged


-- | use previously created reference mapping to remove referenced
-- identifiers from a mapping (leaving only identifiers where they are
-- introduced)
removeReferencedIdentifiers::
  Map.Map LibName (Set.Set IdentifierWON)
  ->Map.Map (LibName, IdentifierWON) (LibName, IdentifierWON)
  ->Map.Map LibName (Set.Set IdentifierWON)
removeReferencedIdentifiers
  flatMap
  identMap =
  let
    newmap =
      foldl
        (\nm (ln, ids) ->
          Set.fold
            (\idwo nm' ->
              case Map.lookup (ln, idwo) identMap of
                Nothing -> Map.insertWith (Set.union) ln (Set.singleton idwo) nm'
                _ -> nm'
            )
            nm
            ids
        )
        Map.empty
        (Map.toList flatMap)
  in
    newmap

-- OMDoc does only enforce unique names inside a theory
-- | Calculate the number of use of a name (attach increasing numbers to
-- multiple occurences of the same name).
--
-- OMDoc allows same names only in different theories (and the names of all
-- theories inside a document must be unique).
getIdUseNumber::
  Map.Map LibName (Set.Set IdentifierWON)
  ->Map.Map LibName (Set.Set (IdentifierWON, Int))
getIdUseNumber
  remMap
  =
  let
    unnMap =
      Map.map
        (\idwoset ->
          let
            maxorigin =
              Set.fold
                (\iwo mo ->
                  max mo (woOrigin iwo)
                )
                0
                idwoset
          in
            foldl
              (\newset currentOrigin ->
                let
                  thisSet =
                    Set.filter
                      (\i -> (woOrigin i) == currentOrigin)
                      idwoset
                  thisNewSet =
                    Set.fold
                      (\iwo tNS ->
                        let
                          usedHere =
                            Set.fold
                              (\(previousIWO,_) uH ->
                                if
                                  (==)
                                    (getIdId $ woItem previousIWO)
                                    (getIdId $ woItem iwo)
                                  then
                                    uH + 1
                                  else
                                    uH
                              )
                              0
                              tNS
                        in
                          Set.insert (iwo, usedHere) tNS
                      )
                      Set.empty
                      thisSet
                in
                  Set.union newset thisNewSet
              )
              Set.empty
              [0..maxorigin]
        )
        remMap
  in
    makeUniqueGlobalCounts unnMap

-- NodeNames and Sentences (Axioms / Definitions) need
-- to be unique in the whole document
-- | fix global namespace issues
makeUniqueGlobalCounts::
  Map.Map LibName (Set.Set (IdentifierWON, Int))
  ->Map.Map LibName (Set.Set (IdentifierWON, Int))
makeUniqueGlobalCounts
  unnMap
  =
  Map.foldWithKey
    (\ln idset m ->
      let
        newidset =
          Set.fold
            (\(wid, c) nis ->
              case woItem wid of
                IdNodeName {} ->
                  let
                    previousUse =
                      Set.fold
                        (\(wid', _) pU ->
                          if
                            (==)
                              (getIdId $ woItem wid')
                              (getIdId $ woItem wid)
                            then
                              pU + 1
                            else
                              pU
                        )
                        (0::Int)
                        nis
                  in
                    Set.insert (wid, previousUse) nis
                IdSens {} ->
                  let
                    previousUse =
                      Set.fold
                        (\(wid', _) pU ->
                          if
                            (==)
                              (getIdId $ woItem wid')
                              (getIdId $ woItem wid)
                            then
                              pU + 1
                            else
                              pU
                        )
                        (0::Int)
                        nis
                  in
                    Set.insert (wid, previousUse) nis
                _ ->
                  Set.insert (wid, c) nis
            )
            Set.empty
            idset
      in
        Map.insert ln newidset m
    )
    Map.empty
    unnMap

{- |
  Create unique names from the use count.

  Name collisions are  handled by numbering names in order of
  appereance and adding \"_\<number>\" to their name. From this
  a second form of collisions arises when there is a \'natural\'
  name in the form of \"name_1\". This algorithm uses the numbering
  as a start and checks uniqueness per theory (and for node-names).
-}
makeUniqueNames::
  Map.Map LibName (Set.Set (IdentifierWON, Int))
  ->Map.Map LibName (Set.Set (IdentifierWON, String))
makeUniqueNames
  countMap
  =
  let
    unnMap =
      Map.map
        (\iwons ->
          let
            (newiwons, _, _) =
              Set.fold
                (\(iwon, c) (ni, nodeNames, inTheoryNames) ->
                  let
                    previousNameSet =
                      case woItem iwon of
                        (IdNodeName {}) -> nodeNames
                        _ ->
                          Map.findWithDefault
                            Set.empty
                            (woOrigin iwon)
                            inTheoryNames
                    finalCount =
                      until
                        (\c' ->
                          let
                            ext = case c' of 0 -> ""; _ -> "_" ++ (show c')
                            name = (show $ getIdId $ woItem iwon) ++ ext
                          in
                            not $ Set.member name previousNameSet
                        )
                        (+1)
                        c
                    finalExt =
                      case finalCount of
                        0 -> ""
                        _ -> "_" ++ (show finalCount)
                    finalName = (show $ getIdId $ woItem iwon) ++ finalExt
                    newSet = Set.insert (iwon, finalName) ni
                    newNameSet = Set.insert finalName previousNameSet
                  in
                    case woItem iwon of
                      (IdNodeName {}) ->
                        (newSet, newNameSet, inTheoryNames)
                      _ ->
                        (
                            newSet
                          , nodeNames
                          , Map.insert (woOrigin iwon) newNameSet inTheoryNames
                        )
                )
                (Set.empty, Set.empty, Map.empty)
                iwons
          in
            newiwons
        )
        countMap
  in
    unnMap


-- | uses a previously generated unique name mapping for identifiers
-- to generated a list of 'IdNameMapping'S for a library environment.
--
-- The mappings contain only the theory unique symbols. See 'makeFullNames'.
makeUniqueIdNameMapping::
  LibEnv
  ->Map.Map LibName (Set.Set (IdentifierWON, String))
  ->[IdNameMapping]
makeUniqueIdNameMapping
  lenv
  unnMap
  =
  foldl
    (\unnames ln ->
      let
        dg = lookupDGraph ln lenv
        ids = Map.findWithDefault Set.empty ln unnMap
        sensfromunn =
          Set.filter
            (\(i, _) -> case woItem i of IdSens {} -> True; _ -> False)
            ids
        gapredsfromunn =
          Set.filter
            (\(i, _) -> case woItem i of IdGaPred {} -> True; _ -> False)
            ids
      in
        foldl
          (\unnames' (nn, node) ->
            let
              nodeids =
                Set.filter
                  (\(i, _) -> woOrigin i == nn)
                  ids
              nodename =
                if not $ isDGRef node
                  then
                    case
                      Set.toList
                        $
                        Set.filter
                          (\(i,_) ->
                            i == mkWON
                                  (IdNodeName
                                    (stringToId
                                      $
                                      nodeNameToName $ dgn_name node
                                    )
                                  )
                                  nn
                          )
                          ids
                    of
                      [] ->
                        trace
                          (
                            "no node found for "
                            ++ show (nn, nodeNameToName $ dgn_name node)
                            ++ "..."
                          )
                          (getDGNodeName node)
                      (_, unName):_ ->
                          unName
                  else
                    let
                      mln = dgn_libname node
                      mdg = lookupDGraph mln lenv
                      mnn = dgn_node node
                      mnode = labDG mdg mnn
                    in
                      case
                        Set.toList
                          $
                          Set.filter
                            (\(i,_) ->
                              i ==
                                mkWON
                                  (IdNodeName
                                    (stringToId
                                      $
                                      nodeNameToName $ dgn_name mnode
                                    )
                                  )
                                  mnn
                            )
                            (Map.findWithDefault Set.empty mln unnMap)
                      of
                        [] -> trace
                          ("no refnode found... "
                            ++ show (ln, nn, nodeNameToName $ dgn_name node)
                            ++ " -> "
                            ++ show (mln, mnn, nodeNameToName $ dgn_name mnode)
                          )
                          (nodeNameToName $ dgn_name mnode)
                        (_, unName):_ -> unName
              remappedsorts =
                Set.map
                  (\(i, uname) ->
                    (getIdId $ woItem i, uname)
                  )
                  (Set.filter
                    (\(i, _) -> case woItem i of IdId {} -> True; _ -> False)
                    nodeids
                  )
              remappedops =
                Set.map
                  (\(i, uname) ->
                    case woItem i of
                      (IdOpM oid ot m _) ->
                        ((oid, ot, m), uname)
                      _ -> error "O!"
                  )
                  (
                    Set.filter
                      (\(i, _) -> case woItem i of
                        IdOpM {} -> True
                        _ -> False
                      )
                      nodeids
                  )
              remappedpreds =
                Set.map
                  (\(i, uname) ->
                    case woItem i of
                      (IdPred pid pt) ->
                        ((pid, pt), uname)
                      _ -> error "P!"
                  )
                  (Set.filter
                    (\(i, _) ->
                      case woItem i of IdPred {} -> True; _ -> False) nodeids
                  )
              nodesensunn = Set.filter (\(i, _) -> woOrigin i == nn) sensfromunn
              nodesens =
                Set.map
                  (\(i, uname) ->
                    case woItem i of
                      (IdSens sensid sennum) ->
                        ((sensid, sennum), uname)
                      _ -> error "Non-sentence found in sentence processing...."
                  )
                nodesensunn
              nodegapredsunn =
                Set.filter (\(i, _) -> woOrigin i == nn) gapredsfromunn
              nodegapreds =
                Set.map
                  (\(i, uname) ->
                    case woItem i of
                      (IdGaPred gapredid gapt) ->
                        ((gapredid, gapt), uname)
                      _ -> error "Non-ga_pred found in ga_pred processing..."
                  )
                  nodegapredsunn
            in
              unnames'
                ++
                [
                  (
                      ln
                    , dgn_name node
                    , nodename
                    , nn
                    , remappedsorts
                    , remappedpreds
                    , remappedops
                    , nodesens
                    , nodegapreds
                  )
                ]
          )
          unnames
          (labNodesDG dg)
    )
    []
    (Map.keys lenv)

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

-- | check type compatibility for two predicates
compatiblePredicate::Rel.Rel SORT->PredType->PredType->Bool
compatiblePredicate sortrel pt1 pt2 =
  compatibleTypes sortrel (predArgs pt1) (predArgs pt2)

-- | check type compatibility for two operators
compatibleOperator::Rel.Rel SORT->OpType->OpType->Bool
compatibleOperator sortrel ot1 ot2 =
--  (\x -> trace ("Comparing " ++ show ot1 ++ " to " ++ show ot2 ++ " -> " ++ show x) x)
--  $
  (isTypeOrSubType sortrel (opRes ot1) (opRes ot2))
  &&
  (compatibleTypes sortrel (opArgs ot1) (opArgs ot2))

type CollectionMap =
  Map.Map
    (LibName, Graph.Node)
    (Map.Map LibName (Set.Set (IdentifierWON, String)))

-- convenience
getIdentifierAt
  ::CollectionMap
  ->(LibName, Graph.Node)
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

getSortsAt
  ::CollectionMap
  ->(LibName, Graph.Node)
  ->[(IdentifierWON, String)]
getSortsAt
  collectionMap
  location
  =
  filter
    (\(i, _) ->
      case woItem i of
        (IdId {}) -> True
        _ -> False
    )
    $
    getIdentifierAt collectionMap location

getPredsAt
  ::CollectionMap
  ->(LibName, Graph.Node)
  ->[((IdentifierWON, PredType), String)]
getPredsAt
  collectionMap
  location
  =
  foldl
    (\l (i, uName) ->
      case woItem i of
        (IdPred _ pt) -> l ++ [((i, pt), uName)]
        (IdGaPred _ pt) -> l ++ [((i, pt), uName)]
        _ -> l
    )
    []
    $
    getIdentifierAt collectionMap location

getOpsAt
  ::CollectionMap
  ->(LibName, Graph.Node)
  ->[((IdentifierWON, OpType), String)]
getOpsAt
  collectionMap
  location
  =
  foldl
    (\l (i, uName) ->
      case woItem i of
        (IdOpM _ ot _ _) -> l ++ [((i, ot), uName)]
        _ -> l
    )
    []
    $
    getIdentifierAt collectionMap location

getSensAt
  ::CollectionMap
  ->(LibName, Graph.Node)
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

-- convenience
getDefinedIdentifierAt
  ::CollectionMap
  ->(LibName, Graph.Node)
  ->[(IdentifierWON, String)]
getDefinedIdentifierAt
  collectionMap
  (location@(llib, _))
  =
  let
    locMap = Map.findWithDefault Map.empty location collectionMap
    defMap = Map.findWithDefault Set.empty llib locMap
  in
    Set.fold
      (\i il ->
        il ++ [i]
      )
      []
      defMap

getDefinedSortsAt
  ::CollectionMap
  ->(LibName, Graph.Node)
  ->[(IdentifierWON, String)]
getDefinedSortsAt
  collectionMap
  location
  =
  filter
    (\(i, _) ->
      case woItem i of
        (IdId {}) -> True
        _ -> False
    )
    $
    getDefinedIdentifierAt collectionMap location

getDefinedPredsAt
  ::CollectionMap
  ->(LibName, Graph.Node)
  ->[((IdentifierWON, PredType), String)]
getDefinedPredsAt
  collectionMap
  location
  =
  foldl
    (\l (i, uName) ->
      case woItem i of
        (IdPred _ pt) -> l ++ [((i, pt), uName)]
        (IdGaPred _ pt) -> l ++ [((i, pt), uName)]
        _ -> l
    )
    []
    $
    getDefinedIdentifierAt collectionMap location

getDefinedOpsAt
  ::CollectionMap
  ->(LibName, Graph.Node)
  ->[((IdentifierWON, OpType), String)]
getDefinedOpsAt
  collectionMap
  location
  =
  foldl
    (\l (i, uName) ->
      case woItem i of
        (IdOpM _ ot _ _) -> l ++ [((i, ot), uName)]
        _ -> l
    )
    []
    $
    getDefinedIdentifierAt collectionMap location

getDefinedSensAt
  ::CollectionMap
  ->(LibName, Graph.Node)
  ->[((IdentifierWON, Int), String)]
getDefinedSensAt
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
    getDefinedIdentifierAt collectionMap location

findIdentifiersForName
  ::CollectionMap
  ->(LibName, Graph.Node)
  ->String
  ->(String->String)
  ->[(LibName, IdentifierWON)]
findIdentifiersForName
  collectionMap
  location
  idname
  stringproc
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
              (\(_, uName) ->
                (stringproc uName) == idname
              )
              s
          )
          locMap
    asList =
      concatMap
        (\(ln, s) ->
          map (\(i, _) -> (ln, i)) $ Set.toList s
        )
        $
        Map.toList
          onlyNames
  in
    asList

findIdIdsForName
  ::CollectionMap
  ->(LibName, Graph.Node)
  ->String
  ->(String->String)
  ->[(LibName, IdentifierWON)]
findIdIdsForName
  collectionMap
  location
  idname
  stringproc
  =
  let
    allValid = findIdentifiersForName collectionMap location idname stringproc
  in
    filter
      (\(_, i) ->
        case woItem i of
          (IdId {}) ->
            True
          _ ->
            False
      )
      allValid

findIdPredsForName
  ::Rel.Rel SORT
  ->PredType
  ->CollectionMap
  ->(LibName, Graph.Node)
  ->String
  ->(String->String)
  ->[(LibName, IdentifierWON)]
findIdPredsForName
  srel
  ptype
  collectionMap
  location
  idname
  stringproc
  =
  let
    allValid = findIdentifiersForName collectionMap location idname stringproc
    compPr =
      filter
        (\(_, i) ->
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
      partition
        (\(_, i) ->
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

findIdOpsForName
  ::Rel.Rel SORT
  ->OpType
  ->CollectionMap
  ->(LibName, Graph.Node)
  ->String
  ->(String->String)
  ->[(LibName, IdentifierWON)]
findIdOpsForName
  srel
  otype
  collectionMap
  location
  idname
  stringproc
  =
  let
    allValid = findIdentifiersForName collectionMap location idname stringproc
    compOp =
      filter
        (\(_, i) ->
          case woItem i of
            (IdOpM _ iot _ _) ->
              compatibleOperator srel iot otype
            _ ->
              False
        )
        allValid
    (eqop, comp) =
      partition
        (\(_, i) ->
          case woItem i of
            (IdOpM _ iot _ _) ->
              iot { opKind = opKind otype } == otype
            _ -> False
        )
        compOp
  in
    if null eqop then comp else eqop

findIdentifiersForId
  ::CollectionMap
  ->(LibName, Graph.Node)
  ->Id
  ->[(LibName, (IdentifierWON, String))]
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


findIdIdsForId
  ::CollectionMap
  ->(LibName, Graph.Node)
  ->Id
  ->[(LibName, (IdentifierWON, String))]
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

findIdPredsForId
  ::Rel.Rel SORT
  ->PredType
  ->CollectionMap
  ->(LibName, Graph.Node)
  ->Id
  ->[(LibName, (IdentifierWON, String))]
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
      partition
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
  ->(LibName, Graph.Node)
  ->Id
  ->[(LibName, (IdentifierWON, String))]
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
        (\(_, (i, _)) ->
          case woItem i of
            (IdOpM _ iot _ _) ->
              compatibleOperator srel iot otype
            _ ->
              False
        )
        allValid
    (eqop, comp) =
      partition
        (\(_, (i, _)) ->
          case woItem i of
            (IdOpM _ iot _ _) ->
              iot { opKind = opKind otype } == otype
            _ -> False
        )
        compOp
  in
    if null eqop then comp else eqop


-- | uses previously generated unique name and reference mappings
-- to generate a mapping for each node showing
-- which symbols are imported from where.
-- By this better statements about the origin of a symbol
-- can be written out (e.g. cdbase)
--
-- See 'makeUniqueIdNameMapping'.
makeCollectionMap::
  LibEnv
  ->Map.Map LibName (Set.Set (IdentifierWON, String))
  ->Map.Map (LibName, IdentifierWON) (LibName, IdentifierWON)
  ->CollectionMap
makeCollectionMap
  lenv
  unnMap
  identMap
  =
  foldl
    (\fnmap ln ->
      let
        dg = lookupDGraph ln lenv
        (sortswomap, predswomap, opswomap) =
          separateIdentifiers
            $
            createNODENAMEWOMap dg
        ids = Map.findWithDefault Set.empty ln unnMap
        sensfromunn =
          Set.filter
            (\(i, _) -> case woItem i of IdSens {} -> True; _ -> False)
            ids
        gapredsfromunn =
          Set.filter
            (\(i, _) -> case woItem i of IdGaPred {} -> True; _ -> False)
            ids
        genopsfromunn =
          Set.filter
            (\(i, _) -> case woItem i of IdOpM _ _ _ True -> True; _ -> False)
            ids
      in
        foldl
          (\fnmap' (nn, node) ->
            let
              nodename =
                if not $ isDGRef node
                  then
                    case
                      Set.toList
                        $
                        Set.filter
                          (\(i,_) ->
                            i ==
                              mkWON
                                (IdNodeName
                                  (stringToId $ nodeNameToName $ dgn_name node)
                                )
                                nn
                          )
                          ids
                    of
                      [] ->
                        trace
                          (
                            "no node found for "
                            ++ show (nn, nodeNameToName $ dgn_name node)
                            ++ "..."
                          )
                          (getDGNodeName node)
                      (_, unName):_ -> unName
                  else
                    let
                      mln = dgn_libname node
                      mdg = lookupDGraph mln lenv
                      mnn = dgn_node node
                      mnode = labDG mdg mnn
                    in
                      case
                        Set.toList
                          $
                          Set.filter
                            (\(i,_) ->
                              i ==
                                mkWON
                                  (IdNodeName
                                    (stringToId $ nodeNameToName $ dgn_name mnode)
                                  )
                                  mnn
                            )
                            (Map.findWithDefault Set.empty mln unnMap)
                      of
                        [] ->
                          trace
                            (
                              "no refnode found... "
                              ++ show (ln, nn, nodeNameToName $ dgn_name node)
                              ++ " -> "
                              ++ show (mln, mnn, nodeNameToName $ dgn_name mnode)
                            )
                            (nodeNameToName $ dgn_name mnode)
                        (_, unName):_ -> unName
              nodesortswo =
                Map.findWithDefault
                  Set.empty
                  (mkWON (dgn_name node) nn)
                  sortswomap
              identsS =
                Set.fold
                  (\swo iMap ->
                    let
                      sasid = mkWON (IdId (woItem swo)) (woOrigin swo)
                    in
                      case Map.lookup (ln, sasid) identMap of
                        Nothing ->
                          case
                            Set.toList
                              $
                              Set.filter
                                (\(i, _) -> i == sasid)
                                ids
                          of
                            [] ->
                              trace
                                (
                                  "In Library " ++ (show ln) ++ ", Theory \""
                                  ++ nodename ++ "\" : Sort " ++ (show swo)
                                  ++ "\" not found!"
                                )
                                $
                                (
                                  Map.insertWith
                                    Set.union
                                    ln
                                    (Set.singleton (sasid, show swo))
                                    iMap
                                )
                            (sid, unName):_ ->
                              Map.insertWith
                                Set.union
                                ln
                                (Set.singleton (sid, unName))
                                iMap
                        (Just (mln, mid)) ->
                          let
                            refIds = Map.findWithDefault Set.empty mln unnMap
                            refSorts =
                              Set.filter
                                (\(s, _) -> case wonItem s of IdId {} -> True; _ -> False)
                                refIds
                            refMatch =
                              Set.filter
                                (\(s,_) -> (getIdId $ wonItem s) == (wonItem swo))
                                refSorts
                            refOrigin =
                              Set.filter
                                (\(s,_) -> (woOrigin s) == (woOrigin mid))
                                refIds
                          in
                            case
                              Set.toList
                                $
                                Set.filter
                                  (\(i, _) -> i == mid)
                                  refIds
                            of
                              [] ->
                                trace
                                  (
                                    "In Library " ++ (show ln) ++ ", Theory \""
                                    ++ nodename ++ "\" : Sort \"" ++ (show swo)
                                    ++ "\" not found, when"
                                    ++ " referencing to it as \""
                                    ++ (show mid) ++ "\" in Library \""
                                    ++ (show mln) ++ "\" "
                                    ++ "Matches by Name : " ++ (show refMatch) ++ " "
                                    ++ "Matches by Origin : " ++ (show refOrigin)
                                  )
                                  $
                                  (
                                    Map.insertWith
                                      Set.union
                                      mln
                                      (Set.singleton (mid, show swo))
                                      iMap
                                  )
                              (_, unName):_ ->
                                Map.insertWith
                                  Set.union
                                  mln
                                  (Set.singleton (mid, unName))
                                  iMap
                  )
                  Map.empty
                  nodesortswo
              nodegenopswo =
                Set.filter (\(i, _) -> woOrigin i == nn) genopsfromunn
              -- generated operators can not be referenced from
              -- somewhere so they are not checked here.
              identsG =
                Set.fold
                  (\(i, uName) iMap ->
                    case woItem i of
                      (IdOpM {}) ->
                        Map.insertWith
                          Set.union
                          ln
                          (Set.singleton (i, uName))
                          iMap
                      _ ->
                        iMap
                  )
                  identsS
                  nodegenopswo
              nodeopswo = Map.findWithDefault Map.empty (mkWON (dgn_name node) nn) opswomap
              identsO =
                Map.foldWithKey
                  (\idwo ots iMap ->
                    Set.fold
                      (\ot iMap' ->
                        let
                          opasid = mkWON (IdOpM (woItem idwo) ot Nothing False) (woOrigin idwo)
                          sid =
                            case Map.lookup (ln, opasid) identMap of
                              Nothing ->
                                case
                                  Set.toList
                                    $
                                    Set.filter
                                      (\(i, _) -> (i == opasid) )
                                      ids
                                of
                                  [] ->
                                    trace
                                      (
                                        "In Library " ++ (show ln) ++ ", Theory \""
                                        ++ nodename ++ "\" : Operator \"" ++ (show idwo)
                                        ++ "\" not found!"
                                      )
                                      (ln, (opasid, show idwo))
                                  (midwo, unName):_ ->
                                    case woItem midwo of
                                      (IdOpM {})  ->
                                        (ln, (midwo, unName))
                                      x ->
                                        trace
                                          ("Not an operator, but same name... " ++ (show x))
                                          (ln, (midwo, unName))
                              (Just (mln, mid)) ->
                                let
                                  refIds = Map.findWithDefault Set.empty mln unnMap
                                  refSorts =
                                    Set.filter
                                      (\(s, _) -> case wonItem s of IdId {} -> True; _ -> False)
                                      refIds
                                  refMatch =
                                    Set.filter
                                      (\(s,_) -> (getIdId $ wonItem s) == (wonItem idwo))
                                      refSorts
                                  refOrigin =
                                    Set.filter
                                      (\(s,_) -> (woOrigin s) == (woOrigin mid))
                                      refIds
                                in
                                  case
                                    Set.toList
                                      $
                                      Set.filter
                                        (\(i, _) -> i == mid)
                                        refIds
                                of
                                  [] ->
                                    trace
                                      (
                                        "In Library " ++ (show ln) ++ ", Theory \""
                                        ++ nodename ++ "\" : Operator \"" ++ (show idwo)
                                        ++ "\" not found, when"
                                        ++ " referencing to it as \""
                                        ++ (show mid) ++ "\" in Library \""
                                        ++ (show mln) ++ "\" "
                                        ++ "Matches by Name : " ++ (show refMatch) ++ " "
                                        ++ "Matches by Origin : " ++ (show refOrigin)
                                      )
                                      (mln, (mid, show idwo))
                                  (midwo, unName):_ ->
                                    case woItem midwo of
                                      (IdOpM {}) ->
                                        (mln, (midwo, unName))
                                      x ->
                                        trace
                                          ("Not an operator but same name " ++ (show x))
                                          (mln, (midwo, unName))

                        in
                          Map.insertWith
                            Set.union
                            (fst sid)
                            (Set.singleton (snd sid))
                            iMap'
                      )
                      iMap
                      ots
                  )
                  identsG
                  nodeopswo
              nodepredswo = Map.findWithDefault Map.empty (mkWON (dgn_name node) nn) predswomap
              identsP =
                Map.foldWithKey
                  (\idwo pts iMap ->
                    Set.fold
                      (\pt iMap' ->
                        let
                          predasid = mkWON (IdPred (woItem idwo) pt) (woOrigin idwo)
                          sid =
                            case Map.lookup (ln, predasid) identMap of
                              Nothing ->
                                case
                                  Set.toList
                                    $
                                    Set.filter
                                      (\(i, _) -> i == predasid)
                                      ids
                                of
                                  [] ->
                                    trace
                                      (
                                        "In Library " ++ (show ln) ++ ", Theory \""
                                        ++ nodename ++ "\" : Predicate \"" ++ (show idwo)
                                        ++ "\" not found!"
                                      )
                                      (ln, (predasid, show idwo))
                                  (pid, unName):_ ->
                                    (ln, (pid, unName))
                              (Just (mln, mid)) ->
                                let
                                  refIds = Map.findWithDefault Set.empty mln unnMap
                                  refSorts =
                                    Set.filter
                                      (\(s, _) -> case wonItem s of IdId {} -> True; _ -> False)
                                      refIds
                                  refMatch =
                                    Set.filter
                                      (\(s,_) -> (getIdId $ wonItem s) == (wonItem idwo))
                                      refSorts
                                  refOrigin =
                                    Set.filter
                                      (\(s,_) -> (woOrigin s) == (woOrigin mid))
                                      refIds
                                in
                                  case
                                    Set.toList
                                      $
                                      Set.filter
                                        (\(i, _) -> i == mid)
                                        refIds
                                  of
                                    [] ->
                                      trace
                                        (
                                          "In Library " ++ (show ln) ++ ", Theory \""
                                          ++ nodename ++ "\" : Predicate \"" ++ (show idwo)
                                          ++ "\" not found, when"
                                          ++ " referencing to it as \""
                                          ++ (show mid) ++ "\" in Library \""
                                          ++ (show mln) ++ "\" "
                                          ++ "Matches by Name : " ++ (show refMatch) ++ " "
                                          ++ "Matches by Origin : " ++ (show refOrigin)
                                        )
                                        (mln, (mid, show idwo))
                                    (pid, unName):_ ->
                                      (mln, (pid, unName))
                        in
                          Map.insertWith
                            Set.union
                            (fst sid)
                            (Set.singleton (snd sid))
                            iMap'
                      )
                      iMap
                      pts
                  )
                  identsO
                  nodepredswo
              nodesensunn = Set.filter (\(i, _) -> woOrigin i == nn) sensfromunn
              identsSen =
                Set.fold
                  (\x iS ->
                    Map.insertWith Set.union ln (Set.singleton x) iS
                  )
                  identsP
                  nodesensunn
              nodegapredsunn =
                Set.filter (\(i, _) -> woOrigin i == nn) gapredsfromunn
              identsGaPred =
                Set.fold
                  (\x iS ->
                    Map.insertWith Set.union ln (Set.singleton x) iS
                  )
                  identsSen
                  nodegapredsunn
            in
              Map.insert (ln, nn) identsGaPred fnmap'
          )
          fnmap
          (labNodesDG dg)
    )
    Map.empty
    (Map.keys lenv)

-- | check if link type is a definitional link but no free or cofree one
isDefLinkType :: DGLinkType -> Bool
isDefLinkType lt = case lt of
  FreeOrCofreeDefLink _ _ -> False
  _ -> isDefEdge lt

-- | check if a link is a definitional link (LocaDef, GlobalDef, HidingDef)
isDefLink :: DGLinkLab -> Bool
isDefLink = isDefLinkType . dgl_type

-- | try to find the origin of an identifier in the DevGraph
traceIdentifierOrigin::
  DGraph -- ^ DevGraph to use
  ->Graph.Node -- ^ start node
  ->Identifier -- ^ Identifier to search origin for
  ->Maybe IdentifierWON
traceIdentifierOrigin
  dg
  n
  identifier
  =
  let
    node = labDG dg n
    caslsign = getJustCASLSign $ getCASLSign $ dgn_sign node
    inEdges = innDG dg n
  in
    case identifier of
      (IdId sid) ->
        let
          sortset = sortSet caslsign
          nonBlockingEdges =
            findNonBlockingEdges
              (Map.toList . sort_map)
              (\(_, tos) i -> tos == i)
              inEdges
        in
          if Set.member sid sortset
            then
              nextTrace nonBlockingEdges
            else
              Nothing
      (IdPred predid predtype) ->
        let
          predmap = predMap caslsign
          nonBlockingEdges =
            findNonBlockingEdges
              (Map.toList . pred_map)
              (\(_, topredid) i -> topredid == i)
              inEdges
        in
          case Map.lookup predid predmap of
            (Just ptset) ->
              if Set.member predtype ptset
                then
                  nextTrace nonBlockingEdges
                else
                  Nothing
            Nothing ->
              Nothing
      (IdOpM opid optype _ _) ->
        let
          opmap = opMap caslsign
          nonBlockingEdges =
            findNonBlockingEdges
              (Map.toList . op_map)
              (\(_, (toopid, _)) i -> toopid == i)
              inEdges
        in
          case Map.lookup opid opmap of
            (Just otset) ->
              if Set.member optype otset
                then
                  nextTrace nonBlockingEdges
                else
                  Nothing
            Nothing ->
              Nothing
      _ -> error "not implemented!"
  where
  nextTrace::[Graph.LEdge DGLinkLab]->Maybe IdentifierWON
  nextTrace
    nbe
    =
    let
      otherNodes =
        map (\(from, _, _) -> from) nbe
      otherTraces =
        map
          (\n' -> traceIdentifierOrigin dg n' identifier)
          otherNodes
    in
      Just
        $
        anythingOr
          (mkWON identifier n)
          otherTraces

  findNonBlockingEdges::
    ((CASL.Morphism.Morphism () () ()) -> [d])
    ->(d->Id->Bool)
    ->[Graph.LEdge DGLinkLab]
    ->[Graph.LEdge DGLinkLab]
  findNonBlockingEdges
    getMorphParts
    checkPart
    inEdges
    =
      filter
        (\(_, _, dgl) ->
          let
            caslmorph = getCASLMorphLL dgl
          in
            (isDefLink dgl)
            &&
            (
            case
              filter
                (\d -> checkPart d (getIdId identifier))
                (getMorphParts caslmorph)
            of
              [] -> True
              _ -> False
            )
        )
      inEdges

-- | try to find the origins of all identifiers in a node
traceAllIdentifierOrigins::
    DGraph -- ^ DevGraph to use
  ->Graph.Node -- ^ node to take identifiers from (to find their origins)
  ->Set.Set IdentifierWON
traceAllIdentifierOrigins
  dg
  n
  =
  let
    node = labDG dg n
    caslsign = getJustCASLSign $ getCASLSign $ dgn_sign node
    sortidentifiers =
      Set.map
        IdId
        (sortSet caslsign)
    predidentifiers =
      Map.foldWithKey
        (\predid ptset pis ->
          let
            piset =
              Set.map
                (\pt -> IdPred predid pt)
                ptset
          in
            Set.union pis piset
        )
        Set.empty
        (predMap caslsign)
    opidentifiers =
      Map.foldWithKey
        (\opid otset ois ->
          let
            oiset =
              Set.map
                (\ot -> IdOpM opid ot Nothing False)
                otset
          in
            Set.union ois oiset
        )
        Set.empty
        (opMap caslsign)
    allIdents = Set.union sortidentifiers $ Set.union predidentifiers opidentifiers
  in
    Set.fold
      (\i iwoset ->
        case
          traceIdentifierOrigin
            dg
            n
            i
        of
          Nothing -> error "should never happen!"
          (Just iwo) -> Set.insert iwo iwoset
      )
      Set.empty
      allIdents

-- | create a mapping of 'Identifier'S with their origins for a DevGraph
createNODENAMEWOMap::
  DGraph
  ->Map.Map NodeNameWO (Set.Set IdentifierWON)
createNODENAMEWOMap
  dg
  =
    getNodeDGNameMappingWO
      dg
      (\dg' n' -> traceAllIdentifierOrigins dg' n')
      Set.null

-- | split a mapping of 'Identifier'S with origins into
-- three mapping. One for sorts, one for predicates and one for operators.
separateIdentifiers::
  Map.Map NodeNameWO (Set.Set IdentifierWON)
  ->(
        SortsMapDGWO
      , PredsMapDGWO
      , OpsMapDGWO
    )
separateIdentifiers
  idmap
  =
  let
    sorts =
      Map.map
        (\iwos ->
          Set.fold
            (\iwo s ->
              case woItem iwo of
                IdId sid ->
                  Set.insert (mkWON sid (woOrigin iwo)) s
                _ -> s
            )
            Set.empty
            iwos
        )
        idmap
    preds =
      Map.map
        (\iwos ->
          Set.fold
            (\iwo p ->
              case woItem iwo of
                IdPred pid pt ->
                  Map.insertWith Set.union (mkWON pid (woOrigin iwo)) (Set.singleton pt) p
                _ -> p
            )
            Map.empty
            iwos
        )
        idmap
    ops =
      Map.map
        (\iwos ->
          Set.fold
            (\iwo o ->
              case woItem iwo of
                (IdOpM oid ot _ _) ->
                  Map.insertWith Set.union (mkWON oid (woOrigin iwo)) (Set.singleton ot) o
                _ -> o
            )
            Map.empty
            iwos
        )
        idmap
  in
    (sorts, preds, ops)


-- | search in a list of name mappings for every mapping that
-- matches a given library name and if it contains an element.
--
-- The /full names/ list is used after the /unique/ list has been searched
-- completely without result.
findOriginInCurrentLib::
  forall a .
  LibName -- ^ only mappings with that library name are searched
  ->[IdNameMapping] -- ^ mapping of unique names
  ->[IdNameMapping] -- ^ mapping of full names (used if nothing found in unique names)
  ->(IdNameMapping->Maybe a) -- ^ search for element
  ->Maybe a
findOriginInCurrentLib
  _
  []
  []
  _
  =
    Nothing
findOriginInCurrentLib
  ln
  (inm:uniqueNames)
  fullNames
  check
  =
    let
      nextsearch = findOriginInCurrentLib ln uniqueNames fullNames check
    in
      if (inmGetLibName inm == ln)
        then
          case check inm of
            Nothing -> nextsearch
            ja -> ja
        else
          nextsearch
findOriginInCurrentLib
  ln
  []
  fullNames
  check
  =
    findOriginInCurrentLib
      ln
      fullNames
      []
      check

traceRealIdentifierOrigins::
  LibEnv
  ->LibName
  ->Graph.Node -- ^ start node
  ->Identifier -- ^ Identifier to search origin for
  ->[IdentifierWON]
traceRealIdentifierOrigins
  lenv
  ln
  n
  identifier
  =
  let
    dg = lookupDGraph ln lenv
    node = labDG dg n
    caslsign = getJustCASLSign $ getCASLSign $ dgn_sign node
    inEdges = innDG dg n
  in
    case identifier of
      (IdId sid) ->
        let
          sortset = sortSet caslsign
          morphismSearches =
            findMorphismSearches
              (Map.toList . sort_map)
              (\(_, tos) i -> tos == i)
              (\(oldname, _) -> IdId oldname)
              dg
              inEdges
          nonBlockingEdges =
            findNonBlockingEdges
              (Map.toList . sort_map)
              (\(_, tos) i -> tos == i)
              inEdges
        in
          if Set.member sid sortset
            then
              nextTraces nonBlockingEdges morphismSearches
            else
              []
      (IdPred predid predtype) ->
        let
          predmap = predMap caslsign
          morphismSearches =
            findMorphismSearches
              (Map.toList . pred_map)
              (\(_, tos) i -> tos == i)
              (\((oldname, oldtype), _) -> IdPred oldname oldtype)
              dg
              inEdges
          nonBlockingEdges =
            findNonBlockingEdges
              (Map.toList . pred_map)
              (\(_, topredid) i -> topredid == i)
              inEdges
        in
          case Map.lookup predid predmap of
            (Just ptset) ->
              if Set.member predtype ptset
                then
                  nextTraces nonBlockingEdges morphismSearches
                else
                  []
            Nothing ->
              []
      (IdOpM opid optype mc isGen) ->
        let
          opmap = opMap caslsign
          morphismSearches =
            findMorphismSearches
              (Map.toList . op_map)
              (\(_, (tos, _)) i -> tos == i)
              (\((oldname, oldtype), _) -> IdOpM oldname oldtype mc isGen)
              dg
              inEdges
          nonBlockingEdges =
            findNonBlockingEdges
              (Map.toList . op_map)
              (\(_, (toopid, _)) i -> toopid == i)
              inEdges
        in
          case Map.lookup opid opmap of
            (Just otset) ->
              if Set.member optype otset
                then
                  nextTraces nonBlockingEdges morphismSearches
                else
                  []
            Nothing ->
              []
      _ -> error "not implemented!"
  where
  nextTraces::[Graph.LEdge DGLinkLab]->[(LibName, Graph.Node, Identifier)]->[IdentifierWON]
  nextTraces nbl mse =
    let
      otherNodes =
        map (\(from, _, _) -> from) nbl
      otherTraces =
        nub
          $
          concatMap
            (\n' -> traceRealIdentifierOrigins lenv ln n' identifier)
            otherNodes
    in
      case otherTraces of
        [] ->
          let
            mSearches =
              nub
                $
                concatMap
                  (\(ln', n', i') ->
                    traceRealIdentifierOrigins lenv ln' n' i'
                  )
                  mse
          in
            case mSearches of
              [] ->
                [mkWON identifier n]
              _ -> mSearches
        _ ->  otherTraces
  findMorphismSearches::
    ((CASL.Morphism.Morphism () () ()) -> [d])
    ->(d->Id->Bool)
    ->(d->Identifier)
    ->DGraph
    ->[(Graph.LEdge DGLinkLab)]
    ->[(LibName, Graph.Node, Identifier)]
  findMorphismSearches
    getMorphParts
    checkPart
    makeNewId
    dg
    inEdges
    =
    foldl
      (\mS (fromNodeNumber, _, dgl) ->
        let
          caslmorph = getCASLMorphLL dgl
          fromNode = labDG dg fromNodeNumber
          (fromlib, fromNodeNum) =
            if isDGRef fromNode
              then
                (dgn_libname fromNode, dgn_node fromNode)
              else
                (ln, fromNodeNumber)
        in
          if not (isDefLink dgl)
            then
              mS
            else
              mS
              ++
              case
                filter
                  (\p -> checkPart p (getIdId identifier))
                  (getMorphParts caslmorph)
              of
                [] ->
                  []
                mlist ->
                  map (\p -> (fromlib, fromNodeNum, makeNewId p)) mlist
      )
      []
      inEdges
  findNonBlockingEdges::
    ((CASL.Morphism.Morphism () () ()) -> [d])
    ->(d->Id->Bool)
    ->[Graph.LEdge DGLinkLab]
    ->[Graph.LEdge DGLinkLab]
  findNonBlockingEdges
    getMorphParts
    checkPart
    inEdges
    =
      filter
        (\(_, _, dgl) ->
          let
            caslmorph = getCASLMorphLL dgl
          in
            (isDefLink dgl)
            &&
            (
            case
              filter
                (\d -> checkPart d (getIdId identifier))
                (getMorphParts caslmorph)
            of
              [] -> True
              _ -> False
            )
        )
      inEdges


traceIdentifierOrigins::
  DGraph -- ^ DevGraph to use
  ->Graph.Node -- ^ start node
  ->Identifier -- ^ Identifier to search origin for
  ->[IdentifierWON]
traceIdentifierOrigins
  dg
  n
  identifier
  =
  let
    node = labDG dg n
    caslsign = getJustCASLSign $ getCASLSign $ dgn_sign node
    inEdges = innDG dg n
  in
    case identifier of
      (IdId sid) ->
        let
          sortset = sortSet caslsign
          nonBlockingEdges =
            filter
              (\(_, _, dgl) ->
                let
                  caslmorph = getCASLMorphLL dgl
                in
                  (isDefLink dgl)
                  &&
                  (
                  case
                    filter
                      (\(_, tos) -> tos == sid)
                      (Map.toList (sort_map caslmorph))
                  of
                    [] -> True
                    _ -> False
                  )
              )
            inEdges
        in
          if Set.member sid sortset
            then
              nextTraces nonBlockingEdges
            else
              []
      (IdPred predid predtype) ->
        let
          predmap = predMap caslsign
          nonBlockingEdges =
            filter
              (\(_, _, dgl) ->
                let
                  caslmorph = getCASLMorphLL dgl
                in
                  (isDefLink dgl)
                  &&
                  (
                  case
                    filter
                      (\(_, topredid) -> topredid == predid)
                      (Map.toList (pred_map caslmorph))
                  of
                    [] -> True
                    _ -> False
                  )
              )
            inEdges
        in
          case Map.lookup predid predmap of
            (Just ptset) ->
              if Set.member predtype ptset
                then
                  nextTraces nonBlockingEdges
                else
                  []
            Nothing ->
              []
      (IdOpM opid optype _ _) ->
        let
          opmap = opMap caslsign
          nonBlockingEdges =
            filter
              (\(_, _, dgl) ->
                let
                  caslmorph = getCASLMorphLL dgl
                in
                  (isDefLink dgl)
                  &&
                  (
                  case
                    filter
                      (\(_, (toopid, _)) -> toopid == opid)
                      (Map.toList (op_map caslmorph))
                  of
                    [] -> True
                    _ -> False
                  )
              )
            inEdges
        in
          case Map.lookup opid opmap of
            (Just otset) ->
              if Set.member optype otset
                then
                  nextTraces nonBlockingEdges
                else
                  []
            Nothing ->
              []
      _ -> error "not implemented!"
  where
  nextTraces::[Graph.LEdge a]->[IdentifierWON]
  nextTraces nbl =
    let
      otherNodes =
        map (\(from, _, _) -> from) nbl
      otherTraces =
        nub
          $
          concatMap
            (\n' -> traceIdentifierOrigins dg n' identifier)
            otherNodes
    in
      case otherTraces of
        [] -> [mkWON identifier n]
        _ ->  otherTraces


-- | try to find all possible origins of all identifiers in a node
traceAllIdentifierOriginsMulti::
    DGraph -- ^ DevGraph to use
  ->Graph.Node -- ^ node to take identifiers from (to find their origins)
  ->Set.Set (Set.Set IdentifierWON)
traceAllIdentifierOriginsMulti
  dg
  n
  =
  let
    node = labDG dg n
    caslsign = getJustCASLSign $ getCASLSign $ dgn_sign node
    sortidentifiers =
      Set.map
        IdId
        (sortSet caslsign)
    predidentifiers =
      Map.foldWithKey
        (\predid ptset pis ->
          let
            piset =
              Set.map
                (\pt -> IdPred predid pt)
                ptset
          in
            Set.union pis piset
        )
        Set.empty
        (predMap caslsign)
    opidentifiers =
      Map.foldWithKey
        (\opid otset ois ->
          let
            oiset =
              Set.map
                (\ot -> IdOpM opid ot Nothing False)
                otset
          in
            Set.union ois oiset
        )
        Set.empty
        (opMap caslsign)
    allIdents = Set.union sortidentifiers $ Set.union predidentifiers opidentifiers
  in
    Set.fold
      (\i iwoset ->
        case
          traceIdentifierOrigins
            dg
            n
            i
        of
          [] -> error "should never happen!"
          iwolist -> Set.insert (Set.fromList iwolist) iwoset
      )
      Set.empty
      allIdents

getMultiOrigins::LibEnv->Map.Map LibName (Set.Set (Set.Set IdentifierWON))
getMultiOrigins lenv =
  foldl
    (\mm ln ->
      let
        dg = lookupDGraph ln lenv
        dgnodes = filter (not . isDGRef . snd) $ labNodesDG dg
      in
        foldl
          (\mm' (nnum, _) ->
            let
              multi = traceAllIdentifierOriginsMulti dg nnum
            in
              Map.insertWith Set.union ln multi mm'
          )
          mm
          dgnodes
    )
    Map.empty
    (Map.keys lenv)
