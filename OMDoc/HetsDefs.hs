{- |
Module      :  $Header$
Copyright   :  (c) Hendrik Iben, Uni Bremen 2005-2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  hiben@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

Additional definitions for interfacing Hets
-}
module OMDoc.HetsDefs
  (
      module Driver.Options
    , module Syntax.AS_Library
    , module Common.GlobalAnnotations
    , dho
    , getFlatNames
    , getMultiOrigins
    , findMultiOriginUnifications
    , traceRealIdentifierOrigins
    , identifyFlatNames
    , removeReferencedIdentifiers
    , getIdUseNumber
    , makeUniqueNames
    , makeFullNames
    , makeUniqueIdNameMapping
    , isDefLink
    , SentenceWO
    , WithOrigin (..)
    , WithOriginNode
    , idToString
    , stringToId
    , NODE_NAMEWO
    , SORTWO
    , getNameForSens
    , IdNameMapping
    , inmGetNodeNum
    , inmGetLibName
    , inmGetIdNameConsSetLikeOps
    , inmGetIdNameSortSet
    , inmGetIdNameOpSet
    , inmGetIdNamePredSet
    , inmGetIdNameGaPredSet
    , inmGetNodeId
    , inmGetNodeName
    , inmGetIdNameConsSet
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
    , getCASLMorphLL
    , getJustCASLSign
    , getCASLSign
    , cv_Op_typeToOpType
    , cv_Pred_typeToPredType
    -- used by input --
    , cv_OpTypeToOp_type
    , cv_PredTypeToPred_type
    , stringToSimpleId
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
    -- unused by may be used
    , getNameForCons
    , getNameOrigins
    , getIdOrigins
    , idToNodeName
    , wonOrigin
  )
  where

import Data.Graph.Inductive.Graph
import qualified Data.Graph.Inductive.Graph as Graph 

import Common.GlobalAnnotations (emptyGlobalAnnos)

import Syntax.AS_Library --(LIB_NAME(),LIB_DEFN()) 

import Driver.Options

import Logic.Grothendieck hiding (Morphism)

import Static.DevGraph

import CASL.AS_Basic_CASL
import CASL.Logic_CASL

import qualified CASL.Induction as Induction

import CASL.Sign
import CASL.Morphism
import qualified CASL.AS_Basic_CASL as CASLBasic
import Data.Typeable
import qualified Common.Id as Id
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Logic.Grothendieck as Gro
import qualified Common.AS_Annotation as Ann
import qualified Data.Maybe as Data.Maybe

import qualified Logic.Prover as Prover

import qualified Common.OrderedMap as OMap

import qualified Common.Result as Result

import qualified Debug.Trace as Debug.Trace

import qualified Data.List as Data.List

import Data.Maybe (fromMaybe)

import OMDoc.Util 

-- | \"alias\" for 'defaultHetcatsOpts' (for export)
dho::HetcatsOpts
dho = defaultHetcatsOpts


-- | Cast Signature to CASLSignature if possible
getCASLSign::G_sign->(Maybe CASLSign)
getCASLSign (G_sign _ sign _) = cast sign 

-- | like a typed /fromMaybe/
getJustCASLSign::(Maybe CASLSign)->CASLSign
getJustCASLSign (Just cs) = cs
getJustCASLSign Nothing = error "Nothing"

-- | Create a simple id ('Id.SIMPLE_ID') from a 'String'
stringToSimpleId::String->Id.SIMPLE_ID
stringToSimpleId = Id.mkSimpleId
       
-- | Shortcut for 'Id.Id' construction from a 'String'
stringToId::String->Id.Id
stringToId = Id.simpleIdToId . Id.mkSimpleId


-- | extract a 'CASL.Morphism.Morphism' from a 'DGLinkLab'
-- will fail if not possible
getCASLMorphLL::DGLinkLab->(CASL.Morphism.Morphism () () ())
getCASLMorphLL edge =
  fromMaybe
    (error "cannot cast morphism to CASL.Morphism")  
    $
    (\(Logic.Grothendieck.GMorphism _ _ _ morph _) -> 
      Data.Typeable.cast morph :: (Maybe (CASL.Morphism.Morphism () () ()))
    ) 
      $
      dgl_morphism edge


-- | This datatype represents /something/ that has an origin.
data WithOrigin a b = WithOrigin { woItem::a, woOrigin::b }
    
-- | 'WithOrigin' specialized to 'Graph.Node' as type of origin.
type WithOriginNode a = WithOrigin a Graph.Node


-- | 'Eq' instance for 'WithOrigin'
-- 
-- Two 'WithOrigin'-objects are equal if their origins are equal and
-- their wrapped elements are equal.
instance (Eq a, Eq b)=>Eq (WithOrigin a b) where
  wo1 == wo2 = ((woOrigin wo1) == (woOrigin wo2)) && ((woItem wo1) == (woItem wo2))  
  
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
getNodeSentences (DGRef {}) = []
getNodeSentences node =
  let
    (Just csen) = (\(G_theory _ _ _ thsens _) -> 
                       (cast thsens)::(Maybe (Prover.ThSens CASLFORMULA 
                                               (AnyComorphism, BasicProof)))) 
                                                 $ dgn_theory node
  in Prover.toNamedList csen

-- | create a mapping over all nodes of a DevGraph
-- where a checker function is provided to filter out
-- unwanted results
getNodeDGNameMappingWO::
  DGraph -- ^ DevGraph to use
  ->(DGraph->Graph.Node->a) -- ^ mapping function
  ->(a->Bool) -- ^ checker function, to determine of the
              -- result of the mapping function is to be kept
  ->(Map.Map NODE_NAMEWO a)
getNodeDGNameMappingWO dg mapper dispose =
   foldl (\mapping (n,node) ->
    let mapped = mapper dg n
    in
    if dispose mapped then
      mapping
    else
      Map.insert (mkWON (dgn_name node) n) mapped mapping
    ) Map.empty $ Graph.labNodes dg


-- added Integer to keep the order of imports (to OMDoc, from OMDoc)
-- | abstract imports
type Imports = Set.Set (Int, (String, HidingAndRequationList, Bool))

-- | node names with origin (node number)
type NODE_NAMEWO = WithOriginNode NODE_NAME

-- | sorts with origin
type SORTWO = WithOriginNode SORT

-- | 'Id.Id'S with origin
type IdWO = WithOriginNode Id.Id

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
type SortsMapDGWO = Map.Map NODE_NAMEWO SortsWO

-- | map of node names with origin to their predicates with origin
type PredsMapDGWO = Map.Map NODE_NAMEWO PredsWO

-- | map of node names with origin to their operators with origin
type OpsMapDGWO = Map.Map NODE_NAMEWO OpsWO

-- | Emptyness test for morphisms.
--
-- Tests for emptyness of sort- function- and predicate-map.
isEmptyMorphism::(Morphism a b c)->Bool
isEmptyMorphism (Morphism _ _ sm fm pm _) =
  Map.null sm && Map.null fm && Map.null pm

-- | returns an empty 'CASL.Morphism.Morphism'
emptyCASLMorphism::(CASL.Morphism.Morphism () () ())
emptyCASLMorphism = CASL.Morphism.Morphism (emptySign ()) (emptySign ()) Map.empty Map.empty Map.empty ()
    
-- | returns an empty 'Logic.Grothendieck.GMorphism' with an internal 'emptyCASLMorphism'
emptyCASLGMorphism::Logic.Grothendieck.GMorphism
emptyCASLGMorphism = Logic.Grothendieck.gEmbed (Logic.Grothendieck.G_morphism CASL  0 emptyCASLMorphism 0 0)

-- | injects a 'CASL.Morphism.Morphism' into a 'Logic.Grothendieck.GMorphism'
makeCASLGMorphism::(CASL.Morphism.Morphism () () ())->Logic.Grothendieck.GMorphism
makeCASLGMorphism m = Logic.Grothendieck.gEmbed (Logic.Grothendieck.G_morphism CASL 0 m 0 0)

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
    

-- | Instance of 'Read' for 'Id.Id'S           
instance Read Id.Id where
  readsPrec _ ('[':s) =
    let
      (tokens, rest) = spanEsc (not . (flip elem "[]")) s
      tokenl = breakIfNonEsc "," tokens
      token = map (\str -> Id.Token (trimString $ unesc str) Id.nullRange) tokenl
      idl = breakIfNonEsc "," rest
      ids = foldl (\ids' str ->
        case ((readsPrec 0 (trimString str))::[(Id.Id, String)]) of
          [] -> error ("Unable to parse \"" ++ str ++ "\"")
          ((newid,_):_) -> ids' ++ [newid]
          ) [] idl
    in
      case (trimString rest) of
        (']':_) -> [(Id.Id token [] Id.nullRange, "")]
        _ -> [(Id.Id token ids Id.nullRange, "")]
      
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

-- | creates a parseable representation of an 'Id.Id' (see Read-instance)
idToString::Id.Id->String
idToString (Id.Id toks ids _) =
                "[" ++
                (implode "," (map (\t -> escapeForId $ Id.tokStr t) toks)) ++
                (implode "," (map idToString ids)) ++
                "]"
                
-- | encapsulates a node_name in an id
nodeNameToId::NODE_NAME->Id.Id
nodeNameToId (s,e,n) = Id.mkId [s,(stringToSimpleId e),(stringToSimpleId (show n))]

-- | reads back an encapsulated node_name
idToNodeName::Id.Id->NODE_NAME
idToNodeName (Id.Id toks _ _) = (toks!!0, show (toks!!1), read (show (toks!!2)))


-- | This type is used for constructing unique names for
-- use in OMDoc-Documents.
--
-- Essential it provides a mapping for a single theory (node) but 
-- these are constructed for a full library environment.
type IdNameMapping =
  (
      LIB_NAME
    , NODE_NAME
    , String
    , Graph.Node
    , Set.Set (Id.Id, String)
    , Set.Set ((Id.Id, PredType), String)
    , Set.Set ((Id.Id, OpType), String)
    , Set.Set ((Id.Id, Int), String)
    , Set.Set ((Int, Id.Id, OpType), String)
    , Set.Set ((Id.Id, PredType), String)
  )


{-
instance Show IdNameMapping where
  show (ln, nn, nsn, nnum, sorts, preds, ops, sens, cons) =
    "(" ++ show ln ++ ", " ++ show nn ++ ", " ++ show nsn ++ ", "
      ++ show nnum ++ ", " ++ show sorts ++ ", " ++ show preds ++ ", "
      ++ show ops ++ ", " ++ show sens ++ ", " ++ show cons ++ ")"
-}

-- | projection function for library name
inmGetLibName::IdNameMapping->LIB_NAME
inmGetLibName (ln, _, _, _, _, _, _, _, _, _) = ln

-- | projection function for node name
inmGetNodeName::IdNameMapping->NODE_NAME
inmGetNodeName (_, nn, _, _, _, _, _, _, _, _) = nn

-- | projection function for XML node name (theory name)
inmGetNodeId::IdNameMapping->String
inmGetNodeId (_, _, id', _, _, _, _, _, _, _) = id'

-- | projection function for node (number)
inmGetNodeNum::IdNameMapping->Graph.Node
inmGetNodeNum (_, _, _, nn, _, _, _, _, _, _) = nn

-- | projection function for the set of sorts
inmGetIdNameSortSet::IdNameMapping->Set.Set (Id.Id, String)
inmGetIdNameSortSet (_, _, _, _, s, _, _, _, _, _) = s

-- | projection function for the disambiguated set of predicates
inmGetIdNamePredSet::IdNameMapping->Set.Set ((Id.Id, PredType), String)
inmGetIdNamePredSet (_, _, _, _, _, s, _, _, _, _) = s

-- | projection function for the disambiguated set of operators
inmGetIdNameOpSet::IdNameMapping->Set.Set ((Id.Id, OpType), String)
inmGetIdNameOpSet (_, _, _, _, _, _, s, _, _, _) = s

-- | projection function for the sentences (annotated by their appearance)
inmGetIdNameSensSet::IdNameMapping->Set.Set ((Id.Id, Int), String)
inmGetIdNameSensSet (_, _, _, _, _, _, _, s, _, _) = s

-- | projection function for the sentences defining sort constructions
-- (annotated by their appearance)
inmGetIdNameConsSet::IdNameMapping->Set.Set ((Int, Id.Id, OpType), String)
inmGetIdNameConsSet (_, _, _, _, _, _, _, _, c, _) = c

-- | conversion function to project constructors ('inmGetIdNameConsSet') like
-- sentences ('inmGetIdNameSensSet')
inmGetIdNameConsSetLikeOps::IdNameMapping->Set.Set ((Id.Id, OpType), String)
inmGetIdNameConsSetLikeOps (_, _, _, _, _, _, _, _, c, _) =
  Set.map
    (\((_, id', ot), name) -> ((id', ot), name))
    c

-- | projection function for the predicates generated by 'Induction.inductionScheme'
inmGetIdNameGaPredSet::IdNameMapping->Set.Set ((Id.Id, PredType), String)
inmGetIdNameGaPredSet (_, _, _, _, _, _, _, _, _, s) = s

-- | get just a set with all known 'Id.Id'S and their XML-names
-- ('Id.Id'S can show up more than once because their XML-name differs).
--
-- This does not contain the 'Id.Id's from 'inmGetIdNameGaPredSet'.
inmGetIdNameAllSet::IdNameMapping->Set.Set (Id.Id, String)
inmGetIdNameAllSet inm =
  Set.union
    (
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
    )
    (
      Set.map
        (\((_, id', _), s') -> (id', s'))
        (inmGetIdNameConsSet inm)
    )

-- | projection function to get library name and node number
inmGetLNNN::IdNameMapping->(LIB_NAME, Graph.Node)
inmGetLNNN inm = (inmGetLibName inm, inmGetNodeNum inm)

-- | searches for mapping where library name and node number match
inmFindLNNN::(LIB_NAME, Graph.Node)->[IdNameMapping]->Maybe IdNameMapping
inmFindLNNN lnnn = Data.List.find (\inm -> inmGetLNNN inm == lnnn)

-- | filter a list of mappings to keep only mappings that contain a
-- given 'Id.Id'
getIdOrigins::[IdNameMapping]->Id.Id->[IdNameMapping]
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

-- | like 'getIdOrigins' but search for an XML-name instead of an 'Id.Id'
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
getNameOrigin::[IdNameMapping]->LIB_NAME->Graph.Node->String->[IdNameMapping]
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
getLNGN::[IdNameMapping]->LIB_NAME->Graph.Node->Maybe IdNameMapping
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
getNameForPred::[IdNameMapping]->(Id.Id, PredType)->Maybe String
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
getNameForOp::[IdNameMapping]->(Id.Id, OpType)->Maybe String
getNameForOp mapping (oid, ot) =
  getNameFor
    mapping
    inmGetIdNameOpSet
    (Set.filter (\((oid', ot'), _) -> oid' == oid && ot' == ot))
    (not . Set.null)
    (snd . head . Set.toList)

-- | search in a list of mappings for the XML-name of a given
-- sentence name (and apperance-tag)
getNameForSens::[IdNameMapping]->(Id.Id, Int)->Maybe String
getNameForSens mapping (s,sn) =
  getNameFor
    mapping
    inmGetIdNameSensSet
    (Set.filter (\((sid, sn'), _) -> sid == s && sn' == sn))
    (not . Set.null)
    (snd . head . Set.toList)

-- | search in a list of mappings for the XML-name of a given
-- constructor (and appearance tag, type)
getNameForCons::[IdNameMapping]->(Int, Id.Id, OpType)->Maybe String
getNameForCons mapping (sennum, cid, ot) =
  getNameFor
    mapping
    inmGetIdNameConsSet
    (Set.filter (\((sennum', cid', ot'), _) -> sennum' == sennum && cid' == cid && ot' == ot))
    (not . Set.null)
    (snd . head . Set.toList)

-- | type conversion. Ommit 'Id.Range'
cv_Op_typeToOpType::OP_TYPE->OpType
cv_Op_typeToOpType (Op_type fk args res _) = OpType fk args res

-- | type conversion. Set range to 'Id.nullRange'.
cv_OpTypeToOp_type::OpType->OP_TYPE
cv_OpTypeToOp_type (OpType fk args res) = Op_type fk args res Id.nullRange

-- | type conversion. Ommit 'Id.Range'
cv_Pred_typeToPredType::PRED_TYPE->PredType
cv_Pred_typeToPredType (Pred_type args _) = PredType args

-- | type conversion. Set range to 'Id.nullRange'.
cv_PredTypeToPred_type::PredType->PRED_TYPE
cv_PredTypeToPred_type (PredType args) = Pred_type args Id.nullRange

-- | translate a named 'CASLFORMULA' into a set of operators
-- corresponding to the /Sort_gen_ax/-axiom.
--
-- Anything else than a /Sort_gen_ax/-axiom for input results in an
-- empty set.
extractConstructorOps::Ann.Named CASLFORMULA->Set.Set (Id.Id, OpType)
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
nodeNameToName::NODE_NAME->String
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
    IdNodeName Id.Id
  | IdId Id.Id
  | IdOp Id.Id OpType
  | IdPred Id.Id PredType
  | IdSens Id.Id Int
  | IdCons Id.Id OpType Int
  -- | for generated predicates ('Induction.inductionScheme')
  | IdGaPred Id.Id PredType
  deriving Show

-- | uniform types for 'Identifier'
data IdentifierType = IdTNodeName | IdTId | IdTOp | IdTPred | IdTSens | IdTCons | IdTGaPred
  deriving (Show, Eq, Ord)

-- | get type for an 'Identifier'
getIdType::Identifier->IdentifierType
getIdType (IdNodeName {}) = IdTNodeName
getIdType (IdId {}) = IdTId
getIdType (IdOp {}) = IdTOp
getIdType (IdPred {}) = IdTPred
getIdType (IdSens {}) = IdTSens
getIdType (IdCons {}) = IdTCons
getIdType (IdGaPred {}) = IdTGaPred

-- | uniformly project the 'Id.Id' an 'Identifier' refers to
getIdId::Identifier->Id.Id
getIdId (IdNodeName i) = i
getIdId (IdId i) = i
getIdId (IdOp i _) = i
getIdId (IdPred i _) = i
getIdId (IdSens i _) = i
getIdId (IdCons i _ _) = i
getIdId (IdGaPred i _) = i

-- | equality for 'Identifier'S. Uses equality of wrapped data
-- (except for disambiguation 'Int'S)
instance Eq Identifier where
  (IdNodeName x) == (IdNodeName y) = x == y
  (IdId x) == (IdId y) = x == y
  (IdOp x xt) == (IdOp y yt) = x == y && xt == yt
  (IdPred x xt) == (IdPred y yt) = x == y && xt == yt
  (IdSens x _) == (IdSens y _) = x == y
  (IdCons x xt _) == (IdCons y yt _) = x == y && xt == yt
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


-- | Collect all used symbols from a library environment.
--
-- Inspects all signatures and sentences and collects generated predicates
-- by extracting them with 'getRecursivePredicates' from the corresponding
-- axioms.
--
-- Uses 'createNODENAMEWOMap' and 'extractConstructorOps'.
getFlatNames::LibEnv->Map.Map LIB_NAME (Set.Set IdentifierWON)
getFlatNames lenv =
  foldl
    (\fm ln ->
      let
        dg = devGraph $ Map.findWithDefault (error "!") ln lenv
        -- extract sorts, predicates and operators
        (sortswomap, predswomap, opswomap) =
          separateIdentifiers
            $
            createNODENAMEWOMap dg 
        dgnodes = filter (not . isDGRef . snd) $ Graph.labNodes dg
        -- collected node names
        nodenameids =
          map
            (\(nn, node) -> (nn, stringToId $ nodeNameToName $ dgn_name node))
            dgnodes
        -- collect and label sentences
        senslist =
          concatMap
            (\(nn, node) -> map (\x -> (nn, x)) $ zip [1..] (getNodeSentences node))
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
                Data.List.nub
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
                                (Just (cf::FORMULA ())) -> 
                                  getRecursivePredicates cf
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
                      Map.insertWith
                        Set.union
                        ln
                        (Set.singleton (mkWON (IdOp (woItem oid) ot) (woOrigin oid)))
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
                (Set.singleton (mkWON (IdSens (stringToId $ Ann.senName namedsen) sennum) nodenum))
                fm'
            )
            preds'
            senslist
        -- process constructors
        cons' =
          foldl
            (\fm' (nodenum, (sennum, cid, cot)) ->
              Map.insertWith
                Set.union
                ln
                (Set.singleton (mkWON (IdCons cid cot sennum) nodenum))
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
  ->Map.Map LIB_NAME (Set.Set IdentifierWON)
  ->Map.Map (LIB_NAME, IdentifierWON) (LIB_NAME, IdentifierWON)
identifyFlatNames
  lenv
  flatmap =
  let
    -- create a list of referenced (external) libraries
    reflist =
      foldl
        (\rl ln ->
          let
            dg = devGraph $ Map.findWithDefault (error "!") ln lenv
            refnodes =
              filter
                (\(_, node) -> isDGRef node)
                (Graph.labNodes dg)
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
                  [] -> Map.insert (refln, rws) (refedln, mkWON (IdId $ stringToId "unknown") refednode) im'
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

-- | find recursive identity matches and reduce targets to real identity.
--
-- Background: import from identifiers that where already imported from
-- somewhere else are not found at first.
fixIdentMap::
    Map.Map (LIB_NAME, IdentifierWON) (LIB_NAME, IdentifierWON)
  ->Map.Map (LIB_NAME, IdentifierWON) (LIB_NAME, IdentifierWON)
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
  ->Map.Map LIB_NAME (Set.Set (Set.Set IdentifierWON))
  ->Map.Map (LIB_NAME, Set.Set IdentifierWON) (LIB_NAME, IdentifierWON)
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
  Map.Map LIB_NAME (Set.Set IdentifierWON)
  ->Map.Map (LIB_NAME, IdentifierWON) (LIB_NAME, IdentifierWON)
  ->Map.Map LIB_NAME (Set.Set IdentifierWON)
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
  Map.Map LIB_NAME (Set.Set IdentifierWON)
  ->Map.Map LIB_NAME (Set.Set (IdentifierWON, Int))
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
  Map.Map LIB_NAME (Set.Set (IdentifierWON, Int))
  ->Map.Map LIB_NAME (Set.Set (IdentifierWON, Int))
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

{-|
  Create unique names from the use count.
 
  Name collisions are  handled by numbering names in order of
  appereance and adding \"_\<number>\" to their name. From this
  a second form of collisions arises when there is a \'natural\'
  name in the form of \"name_1\". This algorithm uses the numbering
  as a start and checks uniqueness per theory (and for node-names).
-}
makeUniqueNames::
  Map.Map LIB_NAME (Set.Set (IdentifierWON, Int))
  ->Map.Map LIB_NAME (Set.Set (IdentifierWON, String))
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
    matchConsWithOps
      unnMap

-- | Some contructors are actually operators. 
--
-- This function fixed the mapping.
matchConsWithOps::
    Map.Map LIB_NAME (Set.Set (IdentifierWON, String))
  ->Map.Map LIB_NAME (Set.Set (IdentifierWON, String))
matchConsWithOps
  unnMap
  =
  Map.map
    (\iwons ->
      Set.map
        (\(iwon, name) ->
          case woItem iwon of
            (IdCons conid _ _) ->
              case
                Set.toList
                  $
                  Set.filter
                    (\(iwon', _) ->
                      case woItem iwon' of
                        (IdOp opid _) ->
                          (opid == conid)
                        _ -> False
                    )
                    iwons
              of
                [] ->
--                 Debug.Trace.trace
--                    ("No Operator for Constructor " ++ (show (iwon, name)))
                    (iwon, name)
                ((_, name'):_) -> (iwon, name')
            _ ->
              (iwon, name)
        )
        iwons
    )
    unnMap

-- | uses a previously generated unique name mapping for identifiers
-- to generated a list of 'IdNameMapping'S for a library environment.
--
-- The mappings contain only the theory unique symbols. See 'makeFullNames'.
makeUniqueIdNameMapping::
  LibEnv
  ->Map.Map LIB_NAME (Set.Set (IdentifierWON, String)) 
  ->[IdNameMapping]
makeUniqueIdNameMapping
  lenv
  unnMap
  =
  foldl
    (\unnames ln ->
      let
        dg = devGraph $ Map.findWithDefault (error "!") ln lenv
        ids = Map.findWithDefault Set.empty ln unnMap
        sensfromunn =
          Set.filter
            (\(i, _) -> case woItem i of IdSens {} -> True; _ -> False)
            ids
        consfromunn =
          Set.filter
            (\(i, _) -> case woItem i of IdCons {} -> True; _ -> False)
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
                        Debug.Trace.trace
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
                      mdg = devGraph $ Map.findWithDefault (error "!") mln lenv
                      mnn = dgn_node node
                      mnode = (\(Just a) -> a) $ Graph.lab mdg mnn
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
                        [] -> Debug.Trace.trace
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
                      (IdOp oid ot) ->
                        ((oid, ot), uname)
                      _ -> error "!"
                  )
                  (
                    Set.filter
                      (\(i, _) -> case woItem i of
                        IdOp {} -> True
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
                      _ -> error "!"
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
              nodeconsunn = Set.filter (\(i, _) -> woOrigin i == nn) consfromunn
              nodecons =
                Set.map
                  (\(i, uname) ->
                    case woItem i of
                      (IdCons conid conot sennum) ->
                        ((sennum, conid, conot), uname)
                      _ -> error "Non-constructor found in constructor processing...."
                  )
                nodeconsunn
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
                    , nodecons
                    , nodegapreds
                  )
                ]
          )
          unnames
          (Graph.labNodes dg)
    )
    []
    (Map.keys lenv)


-- | uses previously generated unique name and reference mappings
-- to generate a list of 'IdNameMapping'S for a library environment
-- containing all used symbols in each theory.
--
-- See 'makeUniqueIdNameMapping'.
makeFullNames::
  LibEnv
  ->Map.Map LIB_NAME (Set.Set (IdentifierWON, String))
  ->Map.Map (LIB_NAME, IdentifierWON) (LIB_NAME, IdentifierWON)
  ->[IdNameMapping]
makeFullNames
  lenv
  unnMap
  identMap
  =
  foldl
    (\fullnames ln ->
      let
        dg = devGraph $ Map.findWithDefault (error "!") ln lenv
        (sortswomap, predswomap, opswomap) =
          separateIdentifiers
            $
            createNODENAMEWOMap dg
        ids = Map.findWithDefault Set.empty ln unnMap
        sensfromunn =
          Set.filter
            (\(i, _) -> case woItem i of IdSens {} -> True; _ -> False)
            ids
        consfromunn =
          Set.filter
            (\(i, _) -> case woItem i of IdCons {} -> True; _ -> False)
            ids
        gapredsfromunn =
          Set.filter
            (\(i, _) -> case woItem i of IdGaPred {} -> True; _ -> False)
            ids
      in
        foldl
          (\fullnames' (nn, node) ->
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
                        Debug.Trace.trace
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
                      mdg = devGraph $ Map.findWithDefault (error "!") mln lenv
                      mnn = dgn_node node
                      mnode = (\(Just a) -> a) $ Graph.lab mdg mnn
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
                          Debug.Trace.trace
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
              remappedsorts =
                Set.map
                  (\swo ->
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
                              Debug.Trace.trace
                                (
                                  "In Library " ++ (show ln) ++ ", Theory \""
                                  ++ nodename ++ "\" : Sort " ++ (show swo)
                                  ++ "\" not found!"
                                )
                                ((woItem swo), show swo)
                            (_, unName):_ -> (woItem swo, unName)
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
                                Debug.Trace.trace
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
                                  ((woItem swo), show swo)
                              (_, unName):_ -> (woItem swo, unName)
                  )
                  nodesortswo
              nodeopswo = Map.findWithDefault Map.empty (mkWON (dgn_name node) nn) opswomap
              remappedops =
                Map.foldWithKey
                  (\idwo ots remops ->
                    Set.fold
                      (\ot ro ->
                        let
                          opasid = mkWON (IdOp (woItem idwo) ot) (woOrigin idwo)
                          newItem = 
                            case Map.lookup (ln, opasid) identMap of
                              Nothing ->
                                case
                                  Set.toList
                                    $
                                    Set.filter
                                      (\(i, _) -> i == opasid)
                                      ids
                                of
                                  [] ->
                                    Debug.Trace.trace
                                      (
                                        "In Library " ++ (show ln) ++ ", Theory \""
                                        ++ nodename ++ "\" : Operator \"" ++ (show idwo)
                                        ++ "\" not found!"
                                      )
                                      (((woItem idwo), ot), show idwo)
                                  (_, unName):_ -> (((woItem idwo), ot), unName)
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
                                    Debug.Trace.trace
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
                                      (((woItem idwo), ot), show idwo)
                                  (_, unName):_ -> (((woItem idwo), ot), unName)
                        in
                          (Set.insert newItem ro)
                      )
                      remops
                      ots
                  )
                  Set.empty
                  nodeopswo
              nodepredswo = Map.findWithDefault Map.empty (mkWON (dgn_name node) nn) predswomap
              remappedpreds =
                Map.foldWithKey
                  (\idwo pts rempreds ->
                    Set.fold
                      (\pt rp ->
                        let
                          predasid = mkWON (IdPred (woItem idwo) pt) (woOrigin idwo)
                          newItem = 
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
                                    Debug.Trace.trace
                                      (
                                        "In Library " ++ (show ln) ++ ", Theory \""
                                        ++ nodename ++ "\" : Predicate \"" ++ (show idwo)
                                        ++ "\" not found!"
                                      )
                                      (((woItem idwo), pt), show idwo)
                                  (_, unName):_ -> (((woItem idwo), pt), unName)
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
                                      Debug.Trace.trace
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
                                        (((woItem idwo), pt), show idwo)
                                    (_, unName):_ -> (((woItem idwo), pt), unName)
                        in
                          (Set.insert newItem rp)
                      )
                      rempreds
                      pts
                  )
                  Set.empty
                  nodepredswo
              nodesensunn = Set.filter (\(i, _) -> woOrigin i == nn) sensfromunn
              nodesens =
                Set.map
                  (\(i, uname) ->
                    case woItem i of
                      (IdSens sensid sennum) ->
                        ((sensid, sennum), uname)
                      _ -> error "Non-sentence found in sentence processing..."
                  )
                nodesensunn
              nodeconsunn = Set.filter (\(i, _) -> woOrigin i == nn) consfromunn
              nodecons =
                Set.map
                  (\(i, uname) ->
                    case woItem i of
                      (IdCons conid conot sennum) ->
                        ((sennum, conid, conot), uname)
                      _ -> error "Non-constructor found in constructor processing..."
                  )
                  nodeconsunn
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
              fullnames'
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
                    , nodecons
                    , nodegapreds
                  )
                ]
          )
          fullnames
          (Graph.labNodes dg)
    )
    []
    (Map.keys lenv)


-- | check if a link is a definitional link (LocaDef, GlobalDef, HidingDef)
isDefLink::DGLinkLab->Bool
isDefLink dgl =
  case dgl_type dgl of
    LocalDef -> True
    GlobalDef -> True
    HidingDef -> True
    _ -> False

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
    node =
      case Graph.lab dg n of
        Nothing -> error "!"
        (Just x) -> x
    caslsign = Data.Maybe.fromMaybe (error "!") $ getCASLSign (dgn_sign node)
    inEdges = Graph.inn dg n
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
      (IdOp opid optype) ->
        let
          opmap = opMap caslsign
          nonBlockingEdges =
            findNonBlockingEdges
              (Map.toList . fun_map)
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
    ->(d->Id.Id->Bool)
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
    node =
      case Graph.lab dg n of
        Nothing -> error "!"
        (Just x) -> x
    caslsign = Data.Maybe.fromMaybe (error "!") $ getCASLSign (dgn_sign node)
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
                (\ot -> IdOp opid ot)
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
  ->Map.Map NODE_NAMEWO (Set.Set IdentifierWON)
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
  Map.Map NODE_NAMEWO (Set.Set IdentifierWON)
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
                IdOp oid ot ->
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
-- matches a fiven library name and if it contains an element.
--
-- The /full names/ list is used after the /unique/ list has been searched 
-- completely without result.
findOriginInCurrentLib::
  forall a .
  LIB_NAME -- ^ only mappings with that library name are searched
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
  ->LIB_NAME
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
    node =
      case Graph.lab dg n of
        Nothing -> error "!"
        (Just x) -> x
    caslsign = Data.Maybe.fromMaybe (error "!") $ getCASLSign (dgn_sign node)
    inEdges = Graph.inn dg n
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
      (IdOp opid optype) ->
        let
          opmap = opMap caslsign
          morphismSearches =
            findMorphismSearches
              (Map.toList . fun_map)
              (\(_, (tos, _)) i -> tos == i)
              (\((oldname, oldtype), _) -> IdOp oldname oldtype)
              dg
              inEdges
          nonBlockingEdges =
            findNonBlockingEdges
              (Map.toList . fun_map)
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
  nextTraces::[Graph.LEdge DGLinkLab]->[(LIB_NAME, Graph.Node, Identifier)]->[IdentifierWON]
  nextTraces nbl mse =
    let
      otherNodes =
        map (\(from, _, _) -> from) nbl
      otherTraces =
        Data.List.nub
          $
          concatMap
            (\n' -> traceRealIdentifierOrigins lenv ln n' identifier)
            otherNodes
    in
      case otherTraces of
        [] ->
          let
            mSearches =
              Data.List.nub
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
    ->(d->Id.Id->Bool)
    ->(d->Identifier)
    ->DGraph
    ->[(Graph.LEdge DGLinkLab)]
    ->[(LIB_NAME, Graph.Node, Identifier)]
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
          fromNode =
            case Graph.lab dg fromNodeNumber of
              Nothing -> error "!"
              (Just x) -> x
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
    ->(d->Id.Id->Bool)
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
    node =
      case Graph.lab dg n of
        Nothing -> error "!"
        (Just x) -> x
    caslsign = Data.Maybe.fromMaybe (error "!") $ getCASLSign (dgn_sign node)
    inEdges = Graph.inn dg n
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
      (IdOp opid optype) ->
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
                      (Map.toList (fun_map caslmorph))
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
        Data.List.nub
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
    node =
      case Graph.lab dg n of
        Nothing -> error "!"
        (Just x) -> x
    caslsign = Data.Maybe.fromMaybe (error "!") $ getCASLSign (dgn_sign node)
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
                (\ot -> IdOp opid ot)
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

getMultiOrigins::LibEnv->Map.Map LIB_NAME (Set.Set (Set.Set IdentifierWON))
getMultiOrigins lenv =
  foldl
    (\mm ln ->  
      let 
        dg = lookupDGraph ln lenv
        dgnodes = filter (not . isDGRef . snd) $ Graph.labNodes dg
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
