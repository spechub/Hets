{-# LANGUAGE RankNTypes, DeriveDataTypeable #-}
{- |
Module      :  ./Static/DevGraph.hs
Description :  Central datastructures for development graphs
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(Logic)

Central datastructures for development graphs
   Follows Sect. IV:4.2 of the CASL Reference Manual.

We also provide functions for constructing and modifying development graphs.
However note that these changes need to be propagated to the GUI if they
also shall be visible in the displayed development graph.
-}

{-
   References:

   T. Mossakowski, S. Autexier and D. Hutter:
   Extending Development Graphs With Hiding.
   H. Hussmann (ed.): Fundamental Approaches to Software Engineering 2001,
   Lecture Notes in Computer Science 2029, p. 269-283,
   Springer-Verlag 2001.

   T. Mossakowski, S. Autexier, D. Hutter, P. Hoffman:
   CASL Proof calculus. In: CASL reference manual, part IV.
   Available from http://www.cofi.info

-}

module Static.DevGraph where

import Syntax.AS_Structured
import Syntax.AS_Library
import Static.GTheory
import Static.DgUtils
import qualified Static.XGraph as XGraph

import Logic.Logic
import Logic.ExtSign
import Logic.Comorphism
import Logic.Grothendieck
import Logic.Prover

import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.Graph as Tree
import qualified Common.Lib.MapSet as MapSet
import qualified Common.Lib.SizedList as SizedList
import qualified Common.OrderedMap as OMap
import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Id
import Common.IRI
import Common.LibName
import Common.Consistency

import Control.Concurrent.MVar

import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Graph as Graph
import Data.Graph.Inductive.Query.DFS

import Data.List
import Data.Maybe
import Data.Ord
import Data.Typeable
import qualified Data.Map as Map
import qualified Data.Set as Set

import Common.Result

-- * types for structured specification analysis

-- ** basic types

-- | Node with signature in a DG
data NodeSig = NodeSig { getNode :: Node, getSig :: G_sign }
    deriving (Show, Eq, Typeable)

{- | NodeSig or possibly the empty sig in a logic
     (but since we want to avoid lots of vsacuous nodes with empty sig,
     we do not assign a real node in the DG here) -}
data MaybeNode = JustNode NodeSig | EmptyNode AnyLogic
  deriving (Show, Eq, Typeable)

getMaybeNodes :: MaybeNode -> Set.Set Node
getMaybeNodes m = case m of
  EmptyNode _ -> Set.empty
  JustNode n -> Set.singleton $ getNode n

-- | a wrapper for renamings with a trivial Ord instance
newtype Renamed = Renamed RENAMING deriving (Show, Typeable)

instance Ord Renamed where
  compare _ _ = EQ

instance Eq Renamed where
  _ == _ = True

-- | a wrapper for restrictions with a trivial Ord instance
data MaybeRestricted = NoRestriction | Restricted RESTRICTION
  deriving (Show, Typeable)

instance Ord MaybeRestricted where
  compare _ _ = EQ

instance Eq MaybeRestricted where
  _ == _ = True

{- | Data type indicating the origin of nodes and edges in the input language
     This is not used in the DG calculus, only may be used in the future
     for reconstruction of input and management of change. -}
data DGOrigin =
    DGEmpty
  | DGBasic
  | DGBasicSpec (Maybe G_basic_spec) G_sign (Set.Set G_symbol)
  | DGExtension
  | DGLogicCoercion
  | DGTranslation Renamed
  | DGUnion
  | DGIntersect
  | DGExtract
  | DGRestriction (MaybeRestricted) (Set.Set G_symbol)
  | DGRevealTranslation
  | DGFreeOrCofree FreeOrCofree
  | DGLocal
  | DGClosed
  | DGLogicQual
  | DGData
  | DGFormalParams
  | DGVerificationGeneric
  | DGImports
  | DGInst IRI
  | DGFitSpec
  | DGFitView IRI
  | DGProof
  | DGNormalForm Node
  | DGintegratedSCC
  | DGFlattening
  | DGAlignment
  | DGTest
    deriving (Show, Eq, Ord, Typeable)

-- | node content or reference to another library's node
data DGNodeInfo = DGNode
  { node_origin :: DGOrigin       -- origin in input language
  , node_cons_status :: ConsStatus } -- like a link from the empty signature
  | DGRef                        -- reference to node in a different DG
  { ref_libname :: LibName      -- pointer to DG where ref'd node resides
  , ref_node :: Node             -- pointer to ref'd node
  } deriving (Show, Eq, Typeable)

{- | node inscriptions in development graphs.
Nothing entries indicate "not computed yet" -}
data DGNodeLab =
  DGNodeLab
  { dgn_name :: NodeName        -- name in the input language
  , dgn_theory :: G_theory      -- local theory
  , globalTheory :: Maybe G_theory -- global theory
  , labelHasHiding :: Bool      -- has this node an ingoing hiding link
  , labelHasFree :: Bool        -- has incoming free definition link
  , dgn_nf :: Maybe Node         -- normal form, for Theorem-Hide-Shift
  , dgn_sigma :: Maybe GMorphism -- inclusion of signature into nf signature
  , dgn_freenf :: Maybe Node -- normal form for freeness
  , dgn_phi :: Maybe GMorphism -- morphism from signature to nffree signature
  , nodeInfo :: DGNodeInfo
  , nodeMod :: NodeMod
  , xnode :: Maybe XGraph.XNode
  , dgn_lock :: Maybe (MVar ())
  } deriving Typeable

instance Show DGNodeLab where
  show _ = "<a DG node label>"

isDGRef :: DGNodeLab -> Bool
isDGRef l = case nodeInfo l of
    DGNode {} -> False
    DGRef {} -> True

sensWithKind :: (forall a . SenStatus a (AnyComorphism, BasicProof) -> Bool)
             -> G_theory -> [String]
sensWithKind f (G_theory _ _ _ _ sens _) = Map.keys $ OMap.filter f sens

hasSenKind :: (forall a . SenStatus a (AnyComorphism, BasicProof) -> Bool)
           -> DGNodeLab -> Bool
hasSenKind f = not . null . sensWithKind f . dgn_theory

-- | test if a given node label has local open goals
hasOpenGoals :: DGNodeLab -> Bool
hasOpenGoals = hasSenKind (\ s -> not (isAxiom s) && not (isProvenSenStatus s))

-- | check if the node has an internal name
isInternalNode :: DGNodeLab -> Bool
isInternalNode DGNodeLab {dgn_name = n} = isInternal n

getNodeConsStatus :: DGNodeLab -> ConsStatus
getNodeConsStatus lbl = case nodeInfo lbl of
   DGRef {} -> mkConsStatus None
   DGNode { node_cons_status = c } -> c

getNodeCons :: DGNodeLab -> Conservativity
getNodeCons = getConsOfStatus . getNodeConsStatus

-- | returns the Conservativity if the given node has one, otherwise none
getNodeConservativity :: LNode DGNodeLab -> Conservativity
getNodeConservativity = getNodeCons . snd

{- | test if a node conservativity is open,
return input for refs or nodes with normal forms -}
hasOpenNodeConsStatus :: Bool -> DGNodeLab -> Bool
hasOpenNodeConsStatus b lbl = if isJust $ dgn_nf lbl then b else
  hasOpenConsStatus b $ getNodeConsStatus lbl

markNodeConsistency :: Conservativity -> String -> DGNodeLab -> DGNodeLab
markNodeConsistency newc str dgnode = dgnode
  { nodeInfo = case nodeInfo dgnode of
      ninfo@DGNode { node_cons_status = ConsStatus c pc thm } ->
          if pc == newc && isProvenThmLinkStatus thm then ninfo else
          ninfo { node_cons_status = ConsStatus c newc
                  $ Proven (DGRule $ showConsistencyStatus newc ++ str)
                    emptyProofBasis }
      ninfo -> ninfo }

markNodeConsistent :: String -> DGNodeLab -> DGNodeLab
markNodeConsistent = markNodeConsistency Cons

markNodeInconsistent :: String -> DGNodeLab -> DGNodeLab
markNodeInconsistent = markNodeConsistency Inconsistent

-- | creates a DGNodeType from a DGNodeLab
getRealDGNodeType :: DGNodeLab -> DGNodeType
getRealDGNodeType dgnlab = DGNodeType
  { isRefType = isDGRef dgnlab
  , isProvenNode = not $ hasOpenGoals dgnlab
  , isProvenCons = not $ hasOpenNodeConsStatus False dgnlab
  , isInternalSpec = isInternalNode dgnlab }

-- | a wrapper for fitting morphisms with a trivial Eq instance
newtype Fitted = Fitted [G_mapping] deriving (Show, Typeable)

instance Eq Fitted where
  _ == _ = True

data DGLinkOrigin =
    SeeTarget
  | SeeSource
  | TEST
  | DGLinkVerif
  | DGImpliesLink
  | DGLinkExtension
  | DGLinkTranslation
  | DGLinkClosedLenv
  | DGLinkImports
  | DGLinkIntersect
  | DGLinkMorph IRI
  | DGLinkInst IRI Fitted
  | DGLinkInstArg IRI
  | DGLinkView IRI Fitted
  | DGLinkAlign IRI
  | DGLinkFitView IRI
  | DGLinkFitViewImp IRI
  | DGLinkProof
  | DGLinkFlatteningUnion
  | DGLinkFlatteningRename
  | DGLinkRefinement IRI
    deriving (Show, Eq, Typeable)

{- | Link types of development graphs,
     Sect. IV:4.2 of the CASL Reference Manual explains them in depth. -}
data DGLinkType =
    ScopedLink Scope LinkKind ConsStatus
  | HidingDefLink
  | FreeOrCofreeDefLink FreeOrCofree MaybeNode -- the "parameter" node
  | HidingFreeOrCofreeThm (Maybe FreeOrCofree) Node GMorphism ThmLinkStatus
    {- DGLink S1 S2 m2 (DGLinkType m1 p) n
    corresponds to a span of morphisms
    S1 <--m1-- S --m2--> S2 -}
    deriving (Show, Eq, Typeable)

-- | extract theorem link status from link type
thmLinkStatus :: DGLinkType -> Maybe ThmLinkStatus
thmLinkStatus t = case t of
    ScopedLink _ (ThmLink s) _ -> Just s
    HidingFreeOrCofreeThm _ _ _ s -> Just s
    _ -> Nothing

-- | extract proof basis from link type
thmProofBasis :: DGLinkType -> ProofBasis
thmProofBasis = maybe emptyProofBasis proofBasisOfThmLinkStatus . thmLinkStatus

updThmProofBasis :: DGLinkType -> ProofBasis -> DGLinkType
updThmProofBasis t pB = case t of
    ScopedLink sc (ThmLink s) cs -> ScopedLink sc
      (ThmLink $ updProofBasisOfThmLinkStatus s pB) cs
    HidingFreeOrCofreeThm h n m s -> HidingFreeOrCofreeThm h n m
      $ updProofBasisOfThmLinkStatus s pB
    _ -> t

-- | link inscriptions in development graphs
data DGLinkLab = DGLink
  { dgl_morphism :: GMorphism  -- signature morphism of link
  , dgl_type :: DGLinkType     -- type: local, global, def, thm?
  , dgl_origin :: DGLinkOrigin -- origin in input language
  , dglPending :: Bool        -- open proofs of edges in proof basis
  , dgl_id :: EdgeId          -- id of the edge
  , dglName :: String         -- name of the edge
  } deriving (Eq, Typeable)

instance Show DGLinkLab where
  show _ = "<a DG link label>"

mkDGLink :: GMorphism -> DGLinkType -> DGLinkOrigin -> String -> EdgeId
         -> DGLinkLab
mkDGLink mor ty orig nn ei = DGLink
  { dgl_morphism = mor
  , dgl_type = ty
  , dgl_origin = orig
  , dglPending = False
  , dgl_id = ei
  , dglName = nn }

-- | name a link
nameDGLink :: String -> DGLinkLab -> DGLinkLab
nameDGLink nn l = l { dglName = nn }

defDGLink :: GMorphism -> DGLinkType -> DGLinkOrigin -> DGLinkLab
{- See svn-version 13804 for a naming concept which unfortunately introduced
same names for different links. -}
defDGLink m ty orig = mkDGLink m ty orig "" defaultEdgeId

defDGLinkId :: GMorphism -> DGLinkType -> DGLinkOrigin -> EdgeId -> DGLinkLab
defDGLinkId m ty orig ei = (defDGLink m ty orig) { dgl_id = ei }

globDefLink :: GMorphism -> DGLinkOrigin -> DGLinkLab
globDefLink m = defDGLink m globalDef

-- | describe the link type of the label
getDGLinkType :: DGLinkLab -> String
getDGLinkType = getDGEdgeTypeName . getRealDGLinkType

getHomEdgeType :: Bool -> Bool -> DGLinkType -> DGEdgeTypeModInc
getHomEdgeType isPend isHom lt = case lt of
      ScopedLink scope lk cons -> case lk of
          DefLink -> case scope of
            Local -> LocalDef
            Global -> if isHom then GlobalDef else HetDef
          ThmLink st -> ThmType
            { thmEdgeType = GlobalOrLocalThm scope isHom
            , isProvenEdge = isProvenThmLinkStatus st
            , isConservativ = isProvenConsStatusLink cons
            , isPending = isPend } -- needs to be checked
      HidingDefLink -> HidingDef
      FreeOrCofreeDefLink fc _ -> FreeOrCofreeDef fc
      HidingFreeOrCofreeThm mh _ _ st -> ThmType
        { thmEdgeType = case mh of
            Nothing -> HidingThm
            Just fc -> FreeOrCofreeThm fc
        , isProvenEdge = isProvenThmLinkStatus st
        , isConservativ = True
        , isPending = isPend }

-- | creates a DGEdgeType from a DGLinkLab
getRealDGLinkType :: DGLinkLab -> DGEdgeType
getRealDGLinkType lnk = let
  gmor = dgl_morphism lnk
  in DGEdgeType
  { edgeTypeModInc = getHomEdgeType (dglPending lnk) (isHomogeneous gmor)
      $ dgl_type lnk
  , isInc = case gmor of
      GMorphism cid _ _ mor _ -> isInclusionComorphism cid && isInclusion mor
  }

-- | return the proof basis of the given linklab
getProofBasis :: DGLinkLab -> ProofBasis
getProofBasis = thmProofBasis . dgl_type

-- | set proof for theorem links
setProof :: ThmLinkStatus -> DGLinkType -> DGLinkType
setProof p lt = case lt of
    ScopedLink sc (ThmLink _) cs -> ScopedLink sc (ThmLink p) cs
    HidingFreeOrCofreeThm hm n mor _ -> HidingFreeOrCofreeThm hm n mor p
    _ -> lt

-- * methods to check the type of an edge

isProven :: DGLinkType -> Bool
isProven edge = case edge of
    ScopedLink _ DefLink _ -> True
    _ -> case thmLinkStatus edge of
           Just (Proven _ _) -> True
           _ -> False

isGlobalEdge :: DGLinkType -> Bool
isGlobalEdge edge = case edge of
    ScopedLink Global _ _ -> True
    _ -> False

isGlobalThm :: DGLinkType -> Bool
isGlobalThm edge = case edge of
    ScopedLink Global (ThmLink _) _ -> True
    _ -> False

isUnprovenGlobalThm :: DGLinkType -> Bool
isUnprovenGlobalThm lt = case lt of
    ScopedLink Global (ThmLink LeftOpen) _ -> True
    _ -> False

isLocalThm :: DGLinkType -> Bool
isLocalThm edge = case edge of
    ScopedLink Local (ThmLink _) _ -> True
    _ -> False

isUnprovenLocalThm :: DGLinkType -> Bool
isUnprovenLocalThm lt = case lt of
    ScopedLink Local (ThmLink LeftOpen) _ -> True
    _ -> False

isUnprovenHidingThm :: DGLinkType -> Bool
isUnprovenHidingThm lt = case lt of
    HidingFreeOrCofreeThm Nothing _ _ LeftOpen -> True
    _ -> False

isFreeEdge :: DGLinkType -> Bool
isFreeEdge edge = case edge of
    FreeOrCofreeDefLink Free _ -> True
    _ -> False

isCofreeEdge :: DGLinkType -> Bool
isCofreeEdge edge = case edge of
    FreeOrCofreeDefLink Cofree _ -> True
    _ -> False

hasOutgoingFreeEdge :: DGraph -> Node -> Bool
hasOutgoingFreeEdge dg n =
 let nEdges = outDG dg n in
 not $ null $ filter (\(_,_, e) -> isFreeEdge $ dgl_type e) nEdges 

-- ** types for global environments

-- | import, formal parameters and united signature of formal params
data GenSig = GenSig MaybeNode [NodeSig] MaybeNode deriving (Show, Typeable)

getGenSigNodes :: GenSig -> Set.Set Node
getGenSigNodes (GenSig m1 ns m2) = Set.unions
  [ getMaybeNodes m1
  , Set.fromList $ map getNode ns
  , getMaybeNodes m2 ]

-- | genericity and body
data ExtGenSig = ExtGenSig
  { genericity :: GenSig
  , extGenBody :: NodeSig }
  deriving (Show, Typeable)

getExtGenSigNodes :: ExtGenSig -> Set.Set Node
getExtGenSigNodes (ExtGenSig g n) = Set.insert (getNode n) $ getGenSigNodes g

-- | source, morphism, parameterized target
data ExtViewSig = ExtViewSig NodeSig GMorphism ExtGenSig
  deriving (Show, Typeable)

getExtViewSigNodes :: ExtViewSig -> Set.Set Node
getExtViewSigNodes (ExtViewSig n _ e) =
  Set.insert (getNode n) $ getExtGenSigNodes e

{- ** types for architectural and unit specification analysis
    (as defined for basic static semantics in Chap. III:5.1) -}

data UnitSig = UnitSig [NodeSig] NodeSig (Maybe NodeSig)
  deriving (Show, Eq, Typeable)
{- Maybe NodeSig stores the union of the parameters
the node is needed for consistency checks -}

getUnitSigNodes :: UnitSig -> Set.Set Node
getUnitSigNodes (UnitSig ns n m) =
  Set.fromList $ map getNode (n : ns ++ maybeToList m)

data ImpUnitSigOrSig = ImpUnitSig MaybeNode UnitSig | Sig NodeSig
   deriving (Show, Eq, Typeable)

type StUnitCtx = Map.Map IRI ImpUnitSigOrSig

emptyStUnitCtx :: StUnitCtx
emptyStUnitCtx = Map.empty

{- data ArchSig = ArchSig StUnitCtx UnitSig deriving (Show, Typeable)
this type is superseeded by RefSig -}

type RefSigMap = Map.Map IRI RefSig

getSigMapNodes :: RefSigMap -> Set.Set Node
getSigMapNodes = Set.unions . map getRefSigNodes . Map.elems

type BStContext = Map.Map IRI RefSig

getBStContextNodes :: BStContext -> Set.Set Node
getBStContextNodes = Set.unions . map getRefSigNodes . Map.elems

-- there should be only BranchRefSigs

data RefSig = BranchRefSig RTPointer (UnitSig, Maybe BranchSig)
            | ComponentRefSig RTPointer RefSigMap
              deriving (Eq, Typeable)

getRefSigNodes :: RefSig -> Set.Set Node
getRefSigNodes rs = case rs of
  BranchRefSig _ (u, m) -> Set.union (getUnitSigNodes u)
    $ maybe Set.empty getBranchSigNodes m
  ComponentRefSig _ m -> getSigMapNodes m

instance Show RefSig where
-- made this instance for debugging purposes
  show (BranchRefSig _ (usig, mbsig)) =
    let bStr = case mbsig of
                 Nothing -> "Bottom\n "
                 Just bsig -> case bsig of
                   UnitSigAsBranchSig u ->
                     if u == usig then "same"
                     else "UnitSigAsBranch:" ++ shows u "\n "
                   BranchStaticContext bst ->
                     foldl (++) "branching: "
                     $ map (\ (n, s) -> shows n " mapped to\n" ++ shows s "\n")
                     $ Map.toList bst
    in
      "Branch: \n before refinement:\n  " ++ show usig ++
      "\n  after refinement: \n" ++ bStr ++ "\n"
  show (ComponentRefSig _ rsm) =
   foldl (++) "CompRefSig:" $ map (\ n -> show n ++ "\n ") $
     Map.toList rsm

getPointerFromRef :: RefSig -> RTPointer
getPointerFromRef (BranchRefSig p _) = p
getPointerFromRef (ComponentRefSig p _) = p

setPointerInRef :: RefSig -> RTPointer -> RefSig
setPointerInRef (BranchRefSig _ x) y = BranchRefSig y x
setPointerInRef (ComponentRefSig _ x) y = ComponentRefSig y x

setUnitSigInRef :: RefSig -> UnitSig -> RefSig
setUnitSigInRef (BranchRefSig x (_, y)) usig = BranchRefSig x (usig, y)
setUnitSigInRef _ _ = error "setUnitSigInRef"

getUnitSigFromRef :: RefSig -> Result UnitSig
getUnitSigFromRef (BranchRefSig _ (usig, _)) = return usig
getUnitSigFromRef (ComponentRefSig _ rsm) =
   error $ "getUnitSigFromRef:" ++ show (Map.keys rsm)

mkRefSigFromUnit :: UnitSig -> RefSig
mkRefSigFromUnit usig = BranchRefSig RTNone
                          (usig, Just $ UnitSigAsBranchSig usig)

mkBotSigFromUnit :: UnitSig -> RefSig
mkBotSigFromUnit usig = BranchRefSig RTNone (usig, Nothing)

data BranchSig = UnitSigAsBranchSig UnitSig
               | BranchStaticContext BStContext
                 deriving (Show, Eq, Typeable)

getBranchSigNodes :: BranchSig -> Set.Set Node
getBranchSigNodes bs = case bs of
  UnitSigAsBranchSig u -> getUnitSigNodes u
  BranchStaticContext b -> getBStContextNodes b

type RefStUnitCtx = Map.Map IRI RefSig
-- only BranchRefSigs allowed

emptyRefStUnitCtx :: RefStUnitCtx
emptyRefStUnitCtx = Map.empty

-- Auxiliaries for refinament signatures composition
matchesContext :: RefSigMap -> BStContext -> Bool
matchesContext rsmap bstc =
  not (any (`notElem` Map.keys bstc) $ Map.keys rsmap)
  && namesMatchCtx (Map.keys rsmap) bstc rsmap

equalSigs :: UnitSig -> UnitSig -> Bool
equalSigs (UnitSig ls1 ns1 _) (UnitSig ls2 ns2 _) =
  length ls1 == length ls2 && getSig ns1 == getSig ns2
    && all (\ (x1, x2) -> getSig x1 == getSig x2) (zip ls1 ls2)

namesMatchCtx :: [IRI] -> BStContext -> RefSigMap -> Bool
namesMatchCtx [] _ _ = True
namesMatchCtx (un : unitNames) bstc rsmap = -- trace ("nMC:" ++ show un)$
 case Map.findWithDefault (error "namesMatchCtx")
            un bstc of
  BranchRefSig _ (_usig, mbsig) -> case mbsig of
    Nothing -> False -- should not be the case
    Just bsig -> case bsig of
     UnitSigAsBranchSig usig' ->
       case Map.findWithDefault (error "USABS") un rsmap of
         BranchRefSig _ (usig'', _mbsig') -> equalSigs usig' usig'' &&
                                         namesMatchCtx unitNames bstc rsmap
         _ -> False
     BranchStaticContext bstc' ->
       case rsmap Map.! un of
         ComponentRefSig _ rsmap' ->
                matchesContext rsmap' bstc' &&
                 namesMatchCtx unitNames bstc rsmap
  {- This is where I introduce something new wrt to the original paper:
  if bstc' has only one element
  it suffices to have the signature of that element
  matching the signature from rsmap' -}
         _ -> Map.size bstc' == 1 &&
                let un1 = head $ Map.keys bstc'
                    rsmap' = Map.mapKeys (\ x -> if x == un then un1 else x)
                               rsmap
                in namesMatchCtx [un1] bstc' rsmap' &&
                   namesMatchCtx unitNames bstc rsmap
  _ -> False -- this should never be the case

modifyCtx :: [IRI] -> RefSigMap -> BStContext -> BStContext
modifyCtx [] _ bstc = bstc
modifyCtx (un : unitNames) rsmap bstc =
 case bstc Map.! un of
   BranchRefSig n1 (usig, mbsig) -> case mbsig of
     Nothing -> modifyCtx unitNames rsmap bstc -- should not be the case
     Just bsig -> case bsig of
       UnitSigAsBranchSig usig' ->
          case rsmap Map.! un of
            BranchRefSig n2 (usig'', bsig'') -> if equalSigs usig' usig'' then
                 modifyCtx unitNames rsmap $
                 Map.insert un (BranchRefSig (compPointer n1 n2)
                            (usig, bsig'')) bstc -- was usig'
                else error "illegal composition"
            _ -> modifyCtx unitNames rsmap bstc
       BranchStaticContext bstc' ->
          case rsmap Map.! un of
            ComponentRefSig n2 rsmap' -> modifyCtx unitNames rsmap $
             Map.insert un
             (BranchRefSig (compPointer n1 n2) (usig, Just $
               BranchStaticContext $ modifyCtx (Map.keys rsmap') rsmap' bstc'))
             bstc
            _ -> let f = if Map.size bstc' == 1 then
                             let un1 = head $ Map.keys bstc'
                                 rsmap' = Map.mapKeys
                                          (\ x -> if x == un then un1 else x)
                                           rsmap
                                 bstc'' = modifyCtx [un1] rsmap' bstc'
                             in Map.singleton un $
                                BranchRefSig RTNone (usig, Just
                                $ BranchStaticContext bstc'')
                           else Map.empty
                 in Map.union f $ modifyCtx unitNames rsmap bstc
   _ -> modifyCtx unitNames rsmap bstc -- same as above

-- Signature composition
refSigComposition :: RefSig -> RefSig -> Result RefSig
refSigComposition (BranchRefSig n1 (usig1, Just (UnitSigAsBranchSig usig2)))
                  (BranchRefSig n2 (usig3, bsig)) =
  if equalSigs usig2 usig3 then
    return $ BranchRefSig (compPointer n1 n2) (usig1, bsig)
    else fail $ "Signatures: \n" ++ show usig2 ++ "\n and \n " ++ show usig3 ++
                "  do not compose"

refSigComposition _rsig1@(BranchRefSig n1
                       (usig1, Just (BranchStaticContext bstc)))
                  _rsig2@(ComponentRefSig n2 rsmap) =
  if matchesContext rsmap bstc then
          return $ BranchRefSig (compPointer n1 n2)
                   (usig1, Just $ BranchStaticContext $
                          modifyCtx (Map.keys rsmap) rsmap bstc)
      else fail ("Signatures do not match:" ++ show (Map.keys bstc) ++ " "
                ++ show (Map.keys rsmap))

refSigComposition (ComponentRefSig n1 rsmap1) (ComponentRefSig n2 rsmap2) = do
  upd <- mapM (\ x -> do
                 s <- refSigComposition (rsmap1 Map.! x) (rsmap2 Map.! x)
                 return (x, s))
         $ filter (`elem` Map.keys rsmap1) $ Map.keys rsmap2
  let unionMap = Map.union (Map.fromList upd) $
                 Map.union rsmap1 rsmap2
  return $ ComponentRefSig (compPointer n1 n2) unionMap

refSigComposition _rsig1 _rsig2 =
  fail "composition of refinement signatures"

-- | an entry of the global environment
data GlobalEntry =
    SpecEntry ExtGenSig
  | ViewOrStructEntry Bool ExtViewSig
  | ArchOrRefEntry Bool RefSig
  | AlignEntry AlignSig
  | UnitEntry UnitSig
  | NetworkEntry GDiagram
  | PatternEntry PatternSig
    deriving (Show, Typeable)

getGlobEntryNodes :: GlobalEntry -> Set.Set Node
getGlobEntryNodes g = case g of
  SpecEntry e -> getExtGenSigNodes e
  ViewOrStructEntry _ e -> getExtViewSigNodes e
  UnitEntry u -> getUnitSigNodes u
  ArchOrRefEntry _ r -> getRefSigNodes r
  NetworkEntry gdiag -> Set.fromList $ nodes gdiag
  _ -> Set.empty

data AlignSig = AlignMor NodeSig GMorphism NodeSig
              | AlignSpan NodeSig GMorphism NodeSig GMorphism NodeSig
              | WAlign
                          NodeSig GMorphism GMorphism -- s1, i1:s1 to b, sig1: s1 to t1
                          NodeSig GMorphism GMorphism -- s2, i2: s2 to b, sig2: s2 to t2
                          NodeSig                     -- t1
                          NodeSig                     -- t2
                          NodeSig                     -- b
  deriving (Show, Eq, Typeable)

-- true for local patterns, imports, list of nodes for those parameters that are ontologies, kinded vars, body
data PatternSig = PatternSig Bool MaybeNode [PatternParamInfo] PatternVarMap LocalOrSpecSig
  deriving (Show, Typeable)

data LocalOrSpecSig = SpecSig LocalOrSpec 
                    | LocalSig (Map.Map IRI PatternSig) LocalOrSpec
                    -- store the varmaps of local subpatterns so they dont get recomputed every time
  deriving (Show, Typeable)

getBody :: LocalOrSpecSig -> LocalOrSpec
getBody (SpecSig x) = x
getBody (LocalSig _ x) = x

data PatternParamInfo = SingleParamInfo Bool NodeSig -- optional or not, node in graph
               | ListParamInfo Int Bool MaybeNode (Maybe IRI)
                 -- length (currrently saves the number of elements before last),
                 --  exact or minimal, node of list template, name of tail if not empty list
               | StringParamInfo IRI
 deriving (Show, Eq, Typeable)
-- TODO: extend for data parameters

type GlobalEnv = Map.Map IRI GlobalEntry

getGlobNodes :: GlobalEnv -> Set.Set Node
getGlobNodes = Set.unions . map getGlobEntryNodes . Map.elems

-- ** change and history types

-- | the edit operations of the DGraph
data DGChange =
    InsertNode (LNode DGNodeLab)
  | DeleteNode (LNode DGNodeLab)
  | InsertEdge (LEdge DGLinkLab)
  | DeleteEdge (LEdge DGLinkLab)
  -- it contains the old label and new label with node
  | SetNodeLab DGNodeLab (LNode DGNodeLab)
  deriving (Show, Typeable)

data HistElem =
    HistElem DGChange
  | HistGroup DGRule ProofHistory
  deriving Typeable

type ProofHistory = SizedList.SizedList HistElem

-- datatypes for the refinement tree

data RTNodeType = RTPlain UnitSig | RTRef Node deriving (Eq, Typeable)

instance Show RTNodeType where
  show (RTPlain u) = "RTPlain\n" ++ show u
  show (RTRef n) = show n

data RTNodeLab = RTNodeLab
  { rtn_type :: RTNodeType
  , rtn_name :: String
  , rtn_diag :: String
  } deriving (Eq, Typeable)

instance Show RTNodeLab where
 show r =
  let
   name = rtn_name r
   t = rtn_type r
   d = rtn_diag r
   t1 = case t of
          RTPlain u -> "plain: " ++ show u
          RTRef n -> show n
  in "Name: " ++ name ++ "\n diag :" ++ d ++ "\n type: " ++ t1

data RTLinkType =
    RTRefine
  | RTComp
  deriving (Show, Eq, Typeable)

data RTLinkLab = RTLink
  { rtl_type :: RTLinkType
  } deriving (Show, Eq, Typeable)

-- utility functions for handling refinement tree

addNodeRT :: DGraph -> UnitSig -> String -> (Node, DGraph)
addNodeRT dg usig s =
 let
  g = refTree dg
  n = Tree.getNewNode g
  l = RTNodeLab {
        rtn_type = RTPlain usig
        , rtn_name = s
        , rtn_diag = s
       }
 in (n, dg {refTree = insNode (n, l) g})

addSpecNodeRT :: DGraph -> UnitSig -> String -> (Node, DGraph)
addSpecNodeRT dg usig s =
 let
  (n, dg') = addNodeRT dg usig s
  f = Map.insert s n $ specRoots dg'
 in (n, dg' {specRoots = f})

updateNodeNameRT :: DGraph -> Node -> Bool -> String -> DGraph
-- the Bool flag tells if the diag name should change too
updateNodeNameRT dg n flag s =
 let
  g = refTree dg
  l = Graph.lab g n
 in case l of
     Nothing -> dg
     Just oldL ->
      let
       newL = if flag then oldL {rtn_name = s, rtn_diag = s}
              else oldL {rtn_name = s}
       (g', _) = Tree.labelNode (n, newL) g
      in dg {refTree = g'}

updateSigRT :: DGraph -> Node -> UnitSig -> DGraph
updateSigRT dg n usig =
 let
  g = refTree dg
  l = Graph.lab g n
 in case l of
     Nothing -> dg
     Just oldL -> let
       newL = oldL {rtn_type = RTPlain usig}
       (g', _) = Tree.labelNode (n, newL) g
                  in dg {refTree = g'}

updateNodeNameSpecRT :: DGraph -> Node -> String -> DGraph
updateNodeNameSpecRT dg n s =
 let dg' = updateNodeNameRT dg n False s
 in dg' {specRoots = Map.insert s n $ specRoots dg}

addSubTree :: DGraph -> Maybe RTLeaves -> RTPointer -> (DGraph, RTPointer)
addSubTree dg Nothing (NPComp h) =
  foldl
   (\ ~(d, NPComp cp) (k, p) -> let
         (d', p') = addSubTree d Nothing p
       in (d', NPComp (Map.insert k p' cp)))
   (dg, NPComp Map.empty) $ Map.toList h
addSubTree dg Nothing p = let
   s = refSource p
   (dg', f) = copySubTree dg s Nothing
   p' = mapRTNodes f p
  in (dg', p')
addSubTree dg (Just (RTLeaf x)) p = let
   s = refSource p
   (dg', f) = copySubTree dg s $ Just x
   p' = mapRTNodes f p
  in (dg', p')
addSubTree dg (Just (RTLeaves g)) (NPComp h) =
 foldl
   (\ ~(d, NPComp cp) (k, p) -> let
         l = Map.findWithDefault (error $ "addSubTree:" ++ show k) k g
         (d', p') = addSubTree d (Just l) p
       in (d', NPComp (Map.insert k p' cp)))
   (dg, NPComp Map.empty) $ Map.toList h
addSubTree _ _ _ = error "addSubTree"

copySubTree :: DGraph -> Node -> Maybe Node -> (DGraph, Map.Map Node Node)
copySubTree dg n mN =
 case mN of
   Nothing -> let
     rTree = refTree dg
     n' = Tree.getNewNode rTree
     nLab = fromMaybe (error "copyNode") $ lab rTree n
     rTree' = insNode (n', nLab) rTree
    in copySubTreeN dg {refTree = rTree'} [n] $ Map.fromList [(n, n')]
   Just y -> copySubTreeN dg [n] $ Map.fromList [(n, y)]

copySubTreeN :: DGraph -> [Node] -> Map.Map Node Node
             -> (DGraph, Map.Map Node Node)
copySubTreeN dg nList pairs =
 case nList of
  [] -> (dg, pairs)
  n : nList' -> let
    rTree = refTree dg
    pairsN = Map.findWithDefault (error "copy") n pairs
    descs = lsuc rTree n
    (dg', pairs') = foldl (copyNode pairsN) (dg, pairs) descs
   in copySubTreeN dg' (nub $ nList' ++ map fst descs) pairs'

copyNode :: Node -> (DGraph, Map.Map Node Node) -> LNode RTLinkLab
           -> (DGraph, Map.Map Node Node)
copyNode s (dg, nMap) (n, eLab) = let
   rTree = refTree dg
   nLab = fromMaybe (error "copyNode") $ lab rTree n
   n' = Tree.getNewNode rTree
   rTree' = insNode (n', nLab) rTree
   orderRT _ _ = GT
   (rTree'', _) = Tree.insLEdge True orderRT (s, n', eLab) rTree'
 in (dg {refTree = rTree''}, Map.insert n n' nMap)

addRefEdgeRT :: DGraph -> Node -> Node -> DGraph
addRefEdgeRT dg n1 n2 =
 let
  g = refTree dg
  orderRT _ _ = GT
  (g', b) = Tree.insLEdge True orderRT
                                 (n1, n2, RTLink {rtl_type = RTRefine}) g
 in if b then dg {refTree = g'}
    else error "addRefEdgeRT"

addEdgesToNodeRT :: DGraph -> [Node] -> Node -> DGraph
addEdgesToNodeRT dg' rnodes n' =
 let
  g = refTree dg'
  orderRT _ _ = GT
  (g', b) = foldl (\ (g0, b0) n0 -> let
                      (g1, b1) = Tree.insLEdge True orderRT
                                 (n', n0, RTLink {rtl_type = RTComp}) g0

                                    in (g1, b1 && b0))
            (g, True) rnodes
 in if not b then error "addEdgesToNodeRT"
    else dg' {refTree = g'}


{- I copied these types from ArchDiagram
to store the diagrams of the arch specs in the dgraph -}

data DiagNodeLab = DiagNode { dn_sig :: NodeSig, dn_desc :: String }
 deriving (Show, Typeable)

data DiagLinkLab = DiagLink { dl_morphism :: GMorphism, dl_number :: Int }
  deriving Typeable

instance Show DiagLinkLab where
 show _ = ""

data Diag = Diagram
  { diagGraph :: Tree.Gr DiagNodeLab DiagLinkLab
  , numberOfEdges :: Int
  } deriving (Show, Typeable)

{- | the actual development graph with auxiliary information. A
  'G_sign' should be stored in 'sigMap' under its 'gSignSelfIdx'. The
  same applies to 'G_morphism' with 'morMap' and 'gMorphismSelfIdx'
  resp. 'G_theory' with 'thMap' and 'gTheorySelfIdx'. -}
data DGraph = DGraph
  { globalAnnos :: GlobalAnnos -- ^ global annos of library
  , optLibDefn :: Maybe LIB_DEFN
  , globalEnv :: GlobalEnv -- ^ name entities (specs, views) of a library
  , dgBody :: Tree.Gr DGNodeLab DGLinkLab  -- ^ actual 'DGraph` tree
  , currentBaseTheory :: Maybe NodeSig
  , refTree :: Tree.Gr RTNodeLab RTLinkLab -- ^ the refinement tree
  , specRoots :: Map.Map String Node -- ^ root nodes for named specs
  , nameMap :: MapSet.MapSet String Node -- ^ all nodes by name
  , archSpecDiags :: Map.Map String Diag
      -- ^ dependency diagrams between units
  , getNewEdgeId :: EdgeId  -- ^ edge counter
  , allRefNodes :: Map.Map (LibName, Node) Node -- ^ all DGRef's
  , sigMap :: Map.Map SigId G_sign -- ^ signature map
  , thMap :: Map.Map ThId G_theory -- ^ theory map
  , morMap :: Map.Map MorId G_morphism -- ^ morphism map
  , proofHistory :: ProofHistory -- ^ applied proof steps
  , redoHistory :: ProofHistory -- ^ undone proofs steps
  } deriving Typeable

instance Show DGraph where
  show _ = "<a development graph>"

emptyDG :: DGraph
emptyDG = DGraph
  { globalAnnos = emptyGlobalAnnos
  , optLibDefn = Nothing
  , globalEnv = Map.empty
  , dgBody = Graph.empty
  , currentBaseTheory = Nothing
  , refTree = Graph.empty
  , specRoots = Map.empty
  , nameMap = MapSet.empty
  , archSpecDiags = Map.empty
  , getNewEdgeId = startEdgeId
  , allRefNodes = Map.empty
  , sigMap = Map.empty
  , thMap = Map.empty
  , morMap = Map.empty
  , proofHistory = SizedList.empty
  , redoHistory = SizedList.empty }

type LibEnv = Map.Map LibName DGraph

-- | an empty environment
emptyLibEnv :: LibEnv
emptyLibEnv = Map.empty

-- * utility functions

-- ** for node signatures

emptyG_sign :: AnyLogic -> G_sign
emptyG_sign (Logic lid) = G_sign lid (ext_empty_signature lid) startSigId

getMaybeSig :: MaybeNode -> G_sign
getMaybeSig (JustNode ns) = getSig ns
getMaybeSig (EmptyNode l) = emptyG_sign l

getLogic :: MaybeNode -> AnyLogic
getLogic = logicOfGsign . getMaybeSig

getNodeLogic :: NodeSig -> AnyLogic
getNodeLogic = logicOfGsign . getSig

-- ** accessing node label

-- | get the origin of a non-reference node (partial)
dgn_origin :: DGNodeLab -> DGOrigin
dgn_origin = node_origin . nodeInfo

-- | get the referenced library (partial)
dgn_libname :: DGNodeLab -> LibName
dgn_libname = ref_libname . nodeInfo

-- | get the referenced node (partial)
dgn_node :: DGNodeLab -> Node
dgn_node = ref_node . nodeInfo

-- | get the signature of a node's theory (total)
dgn_sign :: DGNodeLab -> G_sign
dgn_sign = signOf . dgn_theory

-- | gets the name of a development graph node as a string (total)
getDGNodeName :: DGNodeLab -> String
getDGNodeName = showName . dgn_name

-- | get the global theory of a node or the local one if missing
globOrLocTh :: DGNodeLab -> G_theory
globOrLocTh lbl = fromMaybe (dgn_theory lbl) $ globalTheory lbl

-- ** creating node content and label

-- | create node info
newConsNodeInfo :: DGOrigin -> Conservativity -> DGNodeInfo
newConsNodeInfo orig cs = DGNode
  { node_origin = orig
  , node_cons_status = mkConsStatus cs }

-- | create default content
newNodeInfo :: DGOrigin -> DGNodeInfo
newNodeInfo orig = newConsNodeInfo orig None

-- | create a reference node part
newRefInfo :: LibName -> Node -> DGNodeInfo
newRefInfo ln n = DGRef
  { ref_libname = ln
  , ref_node = n }

-- | create a new node label
newInfoNodeLab :: NodeName -> DGNodeInfo -> G_theory -> DGNodeLab
newInfoNodeLab name info gTh = DGNodeLab
  { dgn_name = name
  , dgn_theory = gTh
  , globalTheory = Nothing
  , labelHasHiding = False
  , labelHasFree = False
  , dgn_nf = Nothing
  , dgn_sigma = Nothing
  , dgn_freenf = Nothing
  , dgn_phi = Nothing
  , nodeInfo = info
  , nodeMod = unMod
  , xnode = Nothing
  , dgn_lock = Nothing }

-- | create a new node label using 'newNodeInfo' and 'newInfoNodeLab'
newNodeLab :: NodeName -> DGOrigin -> G_theory -> DGNodeLab
newNodeLab name = newInfoNodeLab name . newNodeInfo

-- ** handle the lock of a node

-- | wrapper to access the maybe lock
treatNodeLock :: (MVar () -> a) -> DGNodeLab -> a
treatNodeLock f = maybe (error "MVar not initialised") f . dgn_lock

-- | Tries to acquire the local lock. Return False if already acquired.
tryLockLocal :: DGNodeLab -> IO Bool
tryLockLocal = treatNodeLock $ flip tryPutMVar ()

-- | Releases the local lock.
unlockLocal :: DGNodeLab -> IO ()
unlockLocal = treatNodeLock $ \ lock ->
  tryTakeMVar lock >>= maybe (error "Local lock wasn't locked.") return

-- | checks if locking MVar is initialized
hasLock :: DGNodeLab -> Bool
hasLock = isJust . dgn_lock

-- ** edge label equalities

-- | equality without comparing the edge ids
eqDGLinkLabContent :: DGLinkLab -> DGLinkLab -> Bool
eqDGLinkLabContent l1 l2 = let
    i1 = dgl_id l1
    i2 = dgl_id l2
  in (i1 <= defaultEdgeId || i2 <= defaultEdgeId || i1 == i2)
  && dgl_morphism l1 == dgl_morphism l2
  && dgl_type l1 == dgl_type l2
  && dgl_origin l1 == dgl_origin l2
  && dglName l1 == dglName l2

-- | equality comparing ids only
eqDGLinkLabById :: DGLinkLab -> DGLinkLab -> Bool
eqDGLinkLabById l1 l2 = let
    i1 = dgl_id l1
    i2 = dgl_id l2
    in if i1 > defaultEdgeId && i2 > defaultEdgeId then i1 == i2 else
       error "eqDGLinkLabById"

-- ** setting index maps

{- these index maps should be global for all libraries,
   therefore their contents need to be copied -}
cpIndexMaps :: DGraph -> DGraph -> DGraph
cpIndexMaps from to =
  to { sigMap = sigMap from
     , thMap = thMap from
     , morMap = morMap from }

setSigMapDG :: Map.Map SigId G_sign -> DGraph -> DGraph
setSigMapDG m dg = dg { sigMap = m }

setThMapDG :: Map.Map ThId G_theory -> DGraph -> DGraph
setThMapDG m dg = dg { thMap = m }

setMorMapDG :: Map.Map MorId G_morphism -> DGraph -> DGraph
setMorMapDG m dg = dg { morMap = m }

-- ** looking up in index maps

lookupSigMapDG :: SigId -> DGraph -> Maybe G_sign
lookupSigMapDG i = Map.lookup i . sigMap

lookupThMapDG :: ThId -> DGraph -> Maybe G_theory
lookupThMapDG i = Map.lookup i . thMap

lookupMorMapDG :: MorId -> DGraph -> Maybe G_morphism
lookupMorMapDG i = Map.lookup i . morMap

-- ** getting index maps and their maximal index

sigMapI :: DGraph -> (Map.Map SigId G_sign, SigId)
sigMapI = getMapAndMaxIndex startSigId sigMap

thMapI :: DGraph -> (Map.Map ThId G_theory, ThId)
thMapI = getMapAndMaxIndex startThId thMap

morMapI :: DGraph -> (Map.Map MorId G_morphism, MorId)
morMapI = getMapAndMaxIndex startMorId morMap

-- ** lookup other graph parts

lookupGlobalEnvDG :: IRI -> DGraph -> Maybe GlobalEntry
lookupGlobalEnvDG sid dg = let
    gEnv = globalEnv dg
    shortIRI = iriToStringShortUnsecure sid
    in case Map.lookup sid gEnv of
    Nothing -> Map.lookup shortIRI $
               Map.mapKeys iriToStringShortUnsecure gEnv
    m -> m

-- | lookup a reference node for a given libname and node
lookupInAllRefNodesDG :: DGNodeInfo -> DGraph -> Maybe Node
lookupInAllRefNodesDG ref dg = case ref of
    DGRef libn refn ->
        Map.lookup (libn, refn) $ allRefNodes dg
    _ -> Nothing

-- ** lookup nodes by their names or other properties

{- | lookup a node in the graph by its name, using showName
to convert nodenames. -}
lookupNodeByName :: String -> DGraph -> [LNode DGNodeLab]
lookupNodeByName s dg = map (\ n -> (n, labDG dg n)) . Set.toList
  . MapSet.lookup s $ nameMap dg

lookupUniqueNodeByName :: String -> DGraph -> Maybe (LNode DGNodeLab)
lookupUniqueNodeByName s dg =
  case Set.toList $ MapSet.lookup s $ nameMap dg of
    [n] -> do
      l <- lab (dgBody dg) n
      return (n, l)
    _ -> Nothing

{- | filters all local nodes in the graph by their names, using showName
to convert nodenames. See also 'lookupNodeByName'. -}
filterLocalNodesByName :: String -> DGraph -> [LNode DGNodeLab]
filterLocalNodesByName s = filter (not . isDGRef . snd) . lookupNodeByName s

{- | filter all ref nodes in the graph by their names, using showName
to convert nodenames. See also 'lookupNodeByName'. -}
filterRefNodesByName :: String -> LibName -> DGraph -> [LNode DGNodeLab]
filterRefNodesByName s ln =
  filter (\ (_, lbl) -> isDGRef lbl && dgn_libname lbl == ln)
  . lookupNodeByName s

{- | Given a 'LibEnv' we search each DGraph in it for a (maybe referenced) node
 with the given name. We return the labeled node and the Graph where this node
 resides as local node. See also 'lookupLocalNode'. -}
lookupLocalNodeByNameInEnv :: LibEnv -> String
  -> Maybe (DGraph, LNode DGNodeLab)
lookupLocalNodeByNameInEnv le s = f $ Map.elems le where
    f [] = Nothing
    f (dg : l) = case lookupNodeByName s dg of
                 (nd, _) : _ -> Just $ lookupLocalNode le dg nd
                 _ -> f l

{- | We search only the given 'DGraph' for a (maybe referenced) node with the
 given name. We return the labeled node and the Graph where this node resides
 as local node. See also 'lookupLocalNode'. -}
lookupLocalNodeByName :: LibEnv -> DGraph -> String
  -> Maybe (DGraph, LNode DGNodeLab)
lookupLocalNodeByName le dg s =
    case lookupNodeByName s dg of
      (nd, _) : _ -> Just $ lookupLocalNode le dg nd
      _ -> Nothing

{- | Given a Node and a 'DGraph' we follow the node to the graph where it is
 defined as a local node. -}
lookupLocalNode :: LibEnv -> DGraph -> Node -> (DGraph, LNode DGNodeLab)
lookupLocalNode le dg n = let
  (_, refDg, p) = lookupRefNodeM le Nothing dg n
  in (refDg, p)

{- | Given a Node and a 'DGraph' we follow the node to the graph where it is
 defined . -}
lookupRefNode :: LibEnv -> LibName -> DGraph -> Node
   -> (LibName, DGraph, LNode DGNodeLab)
lookupRefNode le ln dg n = let
  (mLn, refDg, p) = lookupRefNodeM le Nothing dg n
  in (fromMaybe ln mLn, refDg, p)

lookupRefNodeM :: LibEnv -> Maybe LibName -> DGraph -> Node
   -> (Maybe LibName, DGraph, LNode DGNodeLab)
lookupRefNodeM le libName dg n = let x = labDG dg n in
  if isDGRef x then let
    ln = dgn_libname x
    n' = dgn_node x in lookupRefNodeM le (Just ln) (lookupDGraph ln le) n'
  else (libName, dg, (n, x))

-- ** accessing the actual graph

-- | get the next available node id
getNewNodeDG :: DGraph -> Node
getNewNodeDG = Tree.getNewNode . dgBody

-- | get all the nodes
labNodesDG :: DGraph -> [LNode DGNodeLab]
labNodesDG = labNodes . dgBody

-- | get all the edges
labEdgesDG :: DGraph -> [LEdge DGLinkLab]
labEdgesDG = labEdges . dgBody

-- | checks if a DG is empty or not.
isEmptyDG :: DGraph -> Bool
isEmptyDG = isEmpty . dgBody

-- | checks if a given node belongs to a given DG
gelemDG :: Node -> DGraph -> Bool
gelemDG n = gelem n . dgBody

-- | get all the incoming ledges of the given node in a given DG
innDG :: DGraph -> Node -> [LEdge DGLinkLab]
innDG = inn . dgBody

-- | get all the outgoing ledges of the given node in a given DG
outDG :: DGraph -> Node -> [LEdge DGLinkLab]
outDG = out . dgBody

-- | get all the nodes of the given DG
nodesDG :: DGraph -> [Node]
nodesDG = nodes . dgBody

-- | tries to get the label of the given node in a given DG
labDG :: DGraph -> Node -> DGNodeLab
labDG dg n = fromMaybe (error $ "labDG " ++ show n) $ lab (dgBody dg) n

-- | tries to get the label of the given node in a given RT
labRT :: DGraph -> Node -> RTNodeLab
labRT dg = fromMaybe (error "labRT") . lab (refTree dg)


-- | get the name of a node from the number of node
getNameOfNode :: Node -> DGraph -> String
getNameOfNode index gc = getDGNodeName $ labDG gc index

-- | gets the given number of new node-ids in a given DG.
newNodesDG :: Int -> DGraph -> [Node]
newNodesDG n = newNodes n . dgBody

-- | get the context and throw input string as error message
safeContextDG :: String -> DGraph -> Node -> Context DGNodeLab DGLinkLab
safeContextDG s = safeContext s . dgBody where
  safeContext err g v = -- same as context with extra message
    fromMaybe (error $ err ++ ": Match Exception, Node: " ++ show v)
    . fst $ match v g

-- ** manipulate graph

-- | sets the node with new label and returns the new graph and the old label
labelNodeDG :: LNode DGNodeLab -> DGraph -> (DGraph, DGNodeLab)
labelNodeDG p@(n, lbl) dg =
    let (b, l) = Tree.labelNode p $ dgBody dg
        oldN = getDGNodeName l
        newN = getDGNodeName lbl
        oldInf = nodeInfo l
        newInf = nodeInfo lbl
        nMap = nameMap dg
        refs = allRefNodes dg
    in (dg { dgBody = b
           , nameMap = if oldN == newN then nMap else
               MapSet.insert newN n $ MapSet.delete oldN n nMap
           , allRefNodes = case (oldInf, newInf) of
               (DGRef libn refn, DGRef nLibn nRefn) ->
                   if newInf == oldInf then refs
                     else Map.insert (nLibn, nRefn) n
                          $ Map.delete (libn, refn) refs
               (DGRef libn refn, _) -> Map.delete (libn, refn) refs
               (_, DGRef nLibn nRefn) -> Map.insert (nLibn, nRefn) n refs
               _ -> refs }, l)

-- | delete the node out of the given DG
delNodeDG :: Node -> DGraph -> DGraph
delNodeDG n dg = case match n $ dgBody dg of
  (Just (_, _, lbl, _), rg) -> let refs = allRefNodes dg in dg
     { dgBody = rg
     , nameMap = MapSet.delete (getDGNodeName lbl) n $ nameMap dg
     , allRefNodes = case nodeInfo lbl of
         DGRef libn refn -> Map.delete (libn, refn) refs
         _ -> refs }
  _ -> error $ "delNodeDG " ++ show n

-- | delete a list of nodes out of the given DG
delNodesDG :: [Node] -> DGraph -> DGraph
delNodesDG = flip $ foldr delNodeDG

-- | insert a new node into given DGraph
insNodeDG :: LNode DGNodeLab -> DGraph -> DGraph
insNodeDG n@(i, l) dg = let refs = allRefNodes dg in dg
  { dgBody = insNode n $ dgBody dg
  , nameMap = MapSet.insert (getDGNodeName l) i $ nameMap dg
  , allRefNodes = case nodeInfo l of
      DGRef libn refn -> Map.insert (libn, refn) i refs
      _ -> refs }

-- | inserts a lnode into a given DG
insLNodeDG :: LNode DGNodeLab -> DGraph -> DGraph
insLNodeDG n@(v, _) g =
    if gelemDG v g then error $ "insLNodeDG " ++ show v else insNodeDG n g

-- | insert a new node with the given node content into a given DGraph
insNodesDG :: [LNode DGNodeLab] -> DGraph -> DGraph
insNodesDG = flip $ foldr insNodeDG

-- | delete a labeled edge out of the given DG
delLEdgeDG :: LEdge DGLinkLab -> DGraph -> DGraph
delLEdgeDG e g = g
    { dgBody = Tree.delLEdge (comparing dgl_id) e
      $ dgBody g }

-- | inserts an edge between two nodes, labelled with inclusion
insInclEdgeDG :: LogicGraph -> DGraph -> NodeSig -> NodeSig ->
                  Result DGraph
insInclEdgeDG lgraph dg s t = do
  incl <- ginclusion lgraph (getSig s) (getSig t)
  let l = globDefLink incl DGLinkImports
      (_, dg') = insLEdgeDG (getNode s, getNode t, l) dg
  return dg'

-- | insert a labeled edge into a given DG, return possibly new id of edge
insLEdgeDG :: LEdge DGLinkLab -> DGraph -> (LEdge DGLinkLab, DGraph)
insLEdgeDG (s, t, l) g =
  let eId = dgl_id l
      nId = getNewEdgeId g
      newId = eId == defaultEdgeId
      e = (s, t, if newId then l { dgl_id = nId } else l)
  in (e, g
    { getNewEdgeId = if newId then incEdgeId nId else max nId $ incEdgeId eId
    , dgBody = fst $ Tree.insLEdge True compareLinks e $ dgBody g })

compareLinks :: DGLinkLab -> DGLinkLab -> Ordering
compareLinks l1 l2 = if eqDGLinkLabContent l1 { dgl_id = defaultEdgeId } l2
        then EQ else comparing dgl_id l1 l2

{- | tries to insert a labeled edge into a given DG, but if this edge
     already exists, then does nothing. -}
insLEdgeNubDG :: LEdge DGLinkLab -> DGraph -> DGraph
insLEdgeNubDG (v, w, l) g =
  let oldEdgeId = getNewEdgeId g
      (ng, change) = Tree.insLEdge False compareLinks
        (v, w, l { dgl_id = oldEdgeId }) $ dgBody g
  in
     g { getNewEdgeId = if change then incEdgeId oldEdgeId else oldEdgeId
       , dgBody = ng }

{- | inserts a new edge into the DGraph using it's own edgeId.
ATTENTION: the caller must ensure that an edgeId is not used twice -}
insEdgeAsIs :: LEdge DGLinkLab -> DGraph -> DGraph
insEdgeAsIs (v, w, l) g = let
  ei = dgl_id l
  in if ei == defaultEdgeId then error "illegal link id" else
     g { dgBody = fst $ Tree.insLEdge False compareLinks
        (v, w, l) $ dgBody g }

-- | insert a list of labeled edge into a given DG
insEdgesDG :: [LEdge DGLinkLab] -> DGraph -> DGraph
insEdgesDG = flip $ foldr insLEdgeNubDG

-- | merge a list of lnodes and ledges into a given DG
mkGraphDG :: [LNode DGNodeLab] -> [LEdge DGLinkLab] -> DGraph -> DGraph
mkGraphDG ns ls = insEdgesDG ls . insNodesDG ns

-- | get links by id (inefficiently)
getDGLinksById :: EdgeId -> DGraph -> [LEdge DGLinkLab]
getDGLinksById e = filter (\ (_, _, l) -> e == dgl_id l) . labEdgesDG

-- | find a unique link given its source node and edgeId
lookupUniqueLink :: Monad m => Node -> EdgeId -> DGraph -> m (LEdge DGLinkLab)
lookupUniqueLink s ei dg = let (Just (_, _, _, outs), _) = match s $ dgBody dg
  in case filter ((== ei) . dgl_id . fst) outs of
    [] -> fail $ "could not find linkId #" ++ show ei
    [(lbl, t)] -> return (s, t, lbl)
    _ -> fail $ "ambigous occurance of linkId #" ++ show ei

-- ** top-level functions

-- | initializes the MVar for locking if nessesary
initLocking :: DGraph -> LNode DGNodeLab -> IO (DGraph, DGNodeLab)
initLocking dg (node, dgn) = do
  lock <- newEmptyMVar
  let dgn' = dgn { dgn_lock = Just lock }
  return (fst $ labelNodeDG (node, dgn') dg, dgn')

-- | returns the DGraph that belongs to the given library name
lookupDGraph :: LibName -> LibEnv -> DGraph
lookupDGraph ln = Map.findWithDefault (error $ "lookupDGraph " ++ show ln) ln

{- | compute the theory of a given node.
   If this node is a DGRef, the referenced node is looked up first. -}
computeLocalTheory :: Monad m => LibEnv -> LibName -> Node -> m G_theory
computeLocalTheory libEnv ln =
  computeLocalNodeTheory libEnv $ lookupDGraph ln libEnv

computeLocalNodeTheory :: Monad m => LibEnv -> DGraph -> Node -> m G_theory
computeLocalNodeTheory libEnv dg = computeLocalLabelTheory libEnv . labDG dg

computeLocalLabelTheory :: Monad m => LibEnv -> DGNodeLab -> m G_theory
computeLocalLabelTheory libEnv nodeLab =
  if isDGRef nodeLab
    then
      computeLocalTheory libEnv (dgn_libname nodeLab) $ dgn_node nodeLab
    else return $ dgn_theory nodeLab

-- ** test link types

liftE :: (DGLinkType -> a) -> LEdge DGLinkLab -> a
liftE f (_, _, edgeLab) = f $ dgl_type edgeLab

isGlobalDef :: DGLinkType -> Bool
isGlobalDef lt = case lt of
    ScopedLink Global DefLink _ -> True
    _ -> False

isLocalDef :: DGLinkType -> Bool
isLocalDef lt = case lt of
    ScopedLink Local DefLink _ -> True
    _ -> False

isHidingDef :: DGLinkType -> Bool
isHidingDef lt = case lt of
    HidingDefLink -> True
    _ -> False

isDefEdge :: DGLinkType -> Bool
isDefEdge edge = case edge of
    ScopedLink _ DefLink _ -> True
    HidingDefLink -> True
    FreeOrCofreeDefLink _ _ -> True
    _ -> False

isLocalEdge :: DGLinkType -> Bool
isLocalEdge edge = case edge of
    ScopedLink Local _ _ -> True
    _ -> False

isHidingEdge :: DGLinkType -> Bool
isHidingEdge edge = case edge of
    HidingDefLink -> True
    HidingFreeOrCofreeThm Nothing _ _ _ -> True
    _ -> False

-- ** create link types

hidingThm :: Node -> GMorphism -> DGLinkType
hidingThm n m = HidingFreeOrCofreeThm Nothing n m LeftOpen

globalThm :: DGLinkType
globalThm = localOrGlobalThm Global None

localThm :: DGLinkType
localThm = localOrGlobalThm Local None

globalConsThm :: Conservativity -> DGLinkType
globalConsThm = localOrGlobalThm Global

localConsThm :: Conservativity -> DGLinkType
localConsThm = localOrGlobalThm Local

localOrGlobalThm :: Scope -> Conservativity -> DGLinkType
localOrGlobalThm sc = ScopedLink sc (ThmLink LeftOpen) . mkConsStatus

localOrGlobalDef :: Scope -> Conservativity -> DGLinkType
localOrGlobalDef sc = ScopedLink sc DefLink . mkConsStatus

globalConsDef :: Conservativity -> DGLinkType
globalConsDef = localOrGlobalDef Global

globalDef :: DGLinkType
globalDef = localOrGlobalDef Global None

localDef :: DGLinkType
localDef = localOrGlobalDef Local None

-- ** link conservativity

getLinkConsStatus :: DGLinkType -> ConsStatus
getLinkConsStatus lt = case lt of
  ScopedLink _ _ c -> c
  _ -> mkConsStatus None

getEdgeConsStatus :: DGLinkLab -> ConsStatus
getEdgeConsStatus = getLinkConsStatus . dgl_type

getCons :: DGLinkType -> Conservativity
getCons = getConsOfStatus . getLinkConsStatus

-- | returns the Conservativity if the given edge has one, otherwise none
getConservativity :: LEdge DGLinkLab -> Conservativity
getConservativity (_, _, edgeLab) = getConsOfStatus $ getEdgeConsStatus edgeLab

-- | returns the conservativity of the given path
getConservativityOfPath :: [LEdge DGLinkLab] -> Conservativity
getConservativityOfPath path = minimum [getConservativity e | e <- path]

-- * bottom up traversal

-- | Creates a LibName relation wrt dependencies via reference nodes
getLibDepRel :: LibEnv -> Rel.Rel LibName
getLibDepRel = Rel.transClosure
  . Rel.fromSet . Map.foldWithKey (\ ln dg s ->
    foldr ((\ x -> if isDGRef x then Set.insert (ln, dgn_libname x) else id)
           . snd) s $ labNodesDG dg) Set.empty

getTopsortedLibs :: LibEnv -> [LibName]
getTopsortedLibs le = let
  rel = getLibDepRel le
  ls = reverse $ topsortedLibsWithImports rel
  restLs = Set.toList $ Set.difference (Map.keysSet le) $ Rel.nodes rel
  in ls ++ restLs

{- | Get imported libs in topological order, i.e.  lib(s) without imports first.
     The input lib-name will be last -}
dependentLibs :: LibName -> LibEnv -> [LibName]
dependentLibs ln le =
  let rel = getLibDepRel le
      ts = topsortedLibsWithImports rel
      is = Set.toList (Rel.succs rel ln)
  in reverse $ ln : intersect ts is

topsortedNodes :: DGraph -> [LNode DGNodeLab]
topsortedNodes dgraph = let dg = dgBody dgraph in
  reverse $ postorderF $ dffWith (\ (_, n, nl, _) -> (n, nl)) (nodes dg)
    $ efilter (\ (s, t, el) -> s /= t && isDefEdge (dgl_type el)) dg

changedPendingEdges :: DGraph -> [LEdge DGLinkLab]
changedPendingEdges dg = let
  ls = filter (liftE $ not . isDefEdge) $ labEdgesDG dg
  (ms, ps) = foldr (\ (s, t, l) (m, es) ->
       let b = dglPending l
           e = dgl_id l
           ty = dgl_type l
       in ( Map.insert e (b, s, t, proofBasis $ thmProofBasis ty) m
          , if b && isLocalEdge ty then Set.insert e es else es))
    (Map.empty, Set.empty) ls
  close known =
      let nxt = Map.keysSet $ Map.filter
                (\ (_, _, _, s) -> not $ Set.null $ Set.intersection s known)
                ms
          new = Set.union nxt known
      in if new == known then new else close new
  aPs = close ps
  in filter (\ (_, _, l) -> dglPending l /= Set.member (dgl_id l) aPs) ls

changedLocalTheorems :: DGraph -> LNode DGNodeLab -> [LEdge DGLinkLab]
changedLocalTheorems dg (v, lbl) =
  case dgn_theory lbl of
    G_theory _ _ _ _ sens _ ->
      foldr (\ e@(_, _, el) l ->
        let pend = dglPending el
            psens = Map.keysSet $ OMap.filter isProvenSenStatus sens
        in case thmLinkStatus $ dgl_type el of
        Just (Proven (DGRuleLocalInference nms) _) | pend
          == Set.isSubsetOf (Set.fromList $ map snd nms) psens -> e : l
        _ -> l
         ) []
      $ filter (liftE $ \ e -> isLocalEdge e && not (isLocalDef e))
      $ innDG dg v

duplicateDefEdges :: DGraph -> [Edge]
duplicateDefEdges = concat .
  filter (not . isSingle) . group . map (\ (s, t, _) -> (s, t))
  . filter (liftE isDefEdge) . labEdgesDG

ensureUniqueNames :: DGraph -> IRI -> Int -> NodeName
ensureUniqueNames dg anIRI n = 
 let allNames = map (getName . dgn_name . snd) $  labNodesDG dg
     iri' = addSuffixToIRI (show n) anIRI
 in if iri' `elem` allNames 
     then ensureUniqueNames dg anIRI (n + 1) 
     else makeName iri'
