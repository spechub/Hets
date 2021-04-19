{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./Static/DgUtils.hs
Description :  auxiliary datastructures for development graphs
Copyright   :  (c) DFKI GmbH 2011
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

-}

module Static.DgUtils where

import qualified Common.Lib.Rel as Rel
import Common.IRI
import Common.Id
import Common.Utils
import Common.LibName
import Common.Consistency

import Data.Data
import Data.List
import Data.Maybe

import qualified Data.Map as Map
import qualified Data.Set as Set

-- ** node label types

data XPathPart = ElemName String | ChildIndex Int deriving (Show, Typeable, Data)

{- | name of a node in a DG; auxiliary nodes may have extension string
     and non-zero number (for these, names are usually hidden). -}
data NodeName = NodeName
  { getName :: IRI
  , extString :: String
  , extIndex :: Int
  , xpath :: [XPathPart]
  , srcRange :: Range
  } deriving (Show, Typeable, Data)

instance Ord NodeName where
  compare n1 n2 = compare (showName n1) (showName n2)

instance Eq NodeName where
  n1 == n2 = compare n1 n2 == EQ

readXPath :: Monad m => String -> m [XPathPart]
readXPath = mapM readXPathComp . splitOn '/'

readXPathComp :: Monad m => String -> m XPathPart
readXPathComp s = case splitAt 5 s of
  ("Spec[", s') -> case readMaybe $ takeWhile (/= ']') s' of
        Just i -> return $ ChildIndex i
        Nothing -> fail "cannot read nodes ChildIndex"
  _ -> return $ ElemName s

isInternal :: NodeName -> Bool
isInternal n = extIndex n /= 0 || not (null $ extString n)

-- | test if a conservativity is open, return input for None
hasOpenConsStatus :: Bool -> ConsStatus -> Bool
hasOpenConsStatus b (ConsStatus cons _ thm) = case cons of
    None -> b
    _ -> not $ isProvenThmLinkStatus thm

data DGNodeType = DGNodeType
  { isRefType :: Bool
  , isProvenNode :: Bool
  , isProvenCons :: Bool
  , isInternalSpec :: Bool }
  deriving (Show, Eq, Ord, Typeable, Data)

listDGNodeTypes :: [DGNodeType]
listDGNodeTypes = let bs = [False, True] in
  [ DGNodeType
    { isRefType = ref
    , isProvenNode = isEmpty'
    , isProvenCons = proven
    , isInternalSpec = spec }
  | ref <- bs
  , isEmpty' <- bs
  , proven <- bs
  , spec <- bs ]

-- | node modifications
data NodeMod = NodeMod
  { delAx :: Bool
  , delTh :: Bool
  , addSen :: Bool
  , delSym :: Bool
  , addSym :: Bool }
  deriving (Show, Eq, Ord, Typeable, Data)

-- | an unmodified node
unMod :: NodeMod
unMod = NodeMod False False False False False

delAxMod :: NodeMod
delAxMod = unMod { delAx = True }

delThMod :: NodeMod
delThMod = unMod { delTh = True }

delSenMod :: NodeMod
delSenMod = delAxMod { delTh = True }

addSenMod :: NodeMod
addSenMod = unMod { addSen = True }

senMod :: NodeMod
senMod = delSenMod { addSen = True }

delSymMod :: NodeMod
delSymMod = unMod { delSym = True }

addSymMod :: NodeMod
addSymMod = unMod { addSym = True }

symMod :: NodeMod
symMod = delSymMod { addSym = True }

mergeNodeMod :: NodeMod -> NodeMod -> NodeMod
mergeNodeMod NodeMod
    { delAx = delAx1
    , delTh = delTh1
    , addSen = addSen1
    , delSym = delSym1
    , addSym = addSym1 }
    NodeMod
    { delAx = delAx2
    , delTh = delTh2
    , addSen = addSen2
    , delSym = delSym2
    , addSym = addSym2 }
    = let delSym3 = delSym1 || delSym2
          setSenMod a b = not delSym3 && (a || b)
    in NodeMod
    { delAx = setSenMod delAx1 delAx2
    , delTh = setSenMod delTh1 delTh2
    , addSen = setSenMod addSen1 addSen2
    , delSym = delSym3
    , addSym = addSym1 || addSym2 }

-- ** edge types

-- | unique number for edges
newtype EdgeId = EdgeId { getEdgeNum :: Int }
  deriving (Eq, Ord, Typeable, Data)

instance Show EdgeId where
  show = show . getEdgeNum

-- | next edge id
incEdgeId :: EdgeId -> EdgeId
incEdgeId (EdgeId i) = EdgeId $ i + 1

-- | the first edge in a graph
startEdgeId :: EdgeId
startEdgeId = EdgeId 0

showEdgeId :: EdgeId -> String
showEdgeId (EdgeId i) = show i

-- | a set of used edges
newtype ProofBasis = ProofBasis { proofBasis :: Set.Set EdgeId }
    deriving (Eq, Ord, Typeable, Data)

instance Show ProofBasis where
  show = show . Set.toList . proofBasis

{- | Rules in the development graph calculus,
   Sect. IV:4.4 of the CASL Reference Manual explains them in depth
-}
data DGRule =
    DGRule String
  | DGRuleWithEdge String EdgeId
  | DGRuleLocalInference [(String, String)] -- renamed theorems
  | Composition [EdgeId]
    deriving (Show, Eq, Ord, Typeable, Data)

-- | proof status of a link
data ThmLinkStatus = LeftOpen | Proven DGRule ProofBasis
  deriving (Show, Eq, Ord, Typeable, Data)

isProvenThmLinkStatus :: ThmLinkStatus -> Bool
isProvenThmLinkStatus tls = case tls of
  LeftOpen -> False
  _ -> True

proofBasisOfThmLinkStatus :: ThmLinkStatus -> ProofBasis
proofBasisOfThmLinkStatus tls = case tls of
  LeftOpen -> emptyProofBasis
  Proven _ pB -> pB

updProofBasisOfThmLinkStatus :: ThmLinkStatus -> ProofBasis -> ThmLinkStatus
updProofBasisOfThmLinkStatus tls pB = case tls of
  LeftOpen -> tls
  Proven r _ -> Proven r pB

data Scope = Local | Global deriving (Show, Eq, Ord, Typeable, Data)

data LinkKind = DefLink | ThmLink ThmLinkStatus
  deriving (Show, Eq, Ord, Typeable, Data)

data FreeOrCofree = Free | Cofree | NPFree | Minimize
  deriving (Show, Eq, Ord, Enum, Bounded, Read, Typeable, Data)

fcList :: [FreeOrCofree]
fcList = [minBound .. maxBound]

-- | required and proven conservativity (with a proof)
data ConsStatus = ConsStatus Conservativity Conservativity ThmLinkStatus
  deriving (Show, Eq, Ord, Typeable, Data)

isProvenConsStatusLink :: ConsStatus -> Bool
isProvenConsStatusLink = not . hasOpenConsStatus False

mkConsStatus :: Conservativity -> ConsStatus
mkConsStatus c = ConsStatus c None LeftOpen

getConsOfStatus :: ConsStatus -> Conservativity
getConsOfStatus (ConsStatus c _ _) = c

-- | to be displayed as edge label
showConsStatus :: ConsStatus -> String
showConsStatus cs = case cs of
  ConsStatus None None _ -> ""
  ConsStatus None _ LeftOpen -> ""
  ConsStatus c _ LeftOpen -> show c ++ "?"
  ConsStatus _ cp _ -> show cp

-- | converts a DGEdgeType to a String
getDGEdgeTypeName :: DGEdgeType -> String
getDGEdgeTypeName e =
  (if isInc e then (++ "Inc") else id)
  $ getDGEdgeTypeModIncName $ edgeTypeModInc e

revertDGEdgeTypeName :: String -> DGEdgeType
revertDGEdgeTypeName tp = fromMaybe (error "DevGraph.revertDGEdgeTypeName")
  $ find ((== tp) . getDGEdgeTypeName) listDGEdgeTypes

getDGEdgeTypeModIncName :: DGEdgeTypeModInc -> String
getDGEdgeTypeModIncName et = case et of
  ThmType thm isPrvn _ _ ->
    let prvn = (if isPrvn then "P" else "Unp") ++ "roven" in
    case thm of
      HidingThm -> prvn ++ "HidingThm"
      FreeOrCofreeThm fc -> prvn ++ shows fc "Thm"
      GlobalOrLocalThm scope isHom ->
          let het = if isHom then id else ("Het" ++) in
          het (case scope of
                 Local -> "Local"
                 Global -> if isHom then "Global" else "") ++ prvn ++ "Thm"
  FreeOrCofreeDef fc -> shows fc "Def"
  _ -> show et

data DGEdgeType = DGEdgeType
  { edgeTypeModInc :: DGEdgeTypeModInc
  , isInc :: Bool }
  deriving (Show, Eq, Ord, Typeable, Data)

data DGEdgeTypeModInc =
    GlobalDef
  | HetDef
  | HidingDef
  | LocalDef
  | FreeOrCofreeDef FreeOrCofree
  | ThmType { thmEdgeType :: ThmTypes
            , isProvenEdge :: Bool
            , isConservativ :: Bool
            , isPending :: Bool }
  deriving (Show, Eq, Ord, Typeable, Data)

data ThmTypes =
    HidingThm
  | FreeOrCofreeThm FreeOrCofree
  | GlobalOrLocalThm { thmScope :: Scope
                     , isHomThm :: Bool }
  deriving (Show, Eq, Ord, Typeable, Data)

-- | Creates a list with all DGEdgeType types
listDGEdgeTypes :: [DGEdgeType]
listDGEdgeTypes =
  [ DGEdgeType { edgeTypeModInc = modinc
               , isInc = isInclusion' }
  | modinc <-
    [ GlobalDef
    , HetDef
    , HidingDef
    , LocalDef
    ] ++ [ FreeOrCofreeDef fc | fc <- fcList ] ++
      [ ThmType { thmEdgeType = thmType
                , isProvenEdge = proven
                , isConservativ = cons
                , isPending = pending }
      | thmType <- HidingThm
        : [ FreeOrCofreeThm fc | fc <- fcList ] ++
          [ GlobalOrLocalThm { thmScope = scope
                             , isHomThm = hom }
          | scope <- [Local, Global]
          , hom <- [True, False]
          ]
      , proven <- [True, False]
      , cons <- [True, False]
      , pending <- [True, False]
      ]
  , isInclusion' <- [True, False]
  ]

-- | check an EdgeType and see if its a definition link
isDefEdgeType :: DGEdgeType -> Bool
isDefEdgeType edgeTp = case edgeTypeModInc edgeTp of
    ThmType {} -> False
    _ -> True


-- * datatypes for storing the nodes of the ref tree in the global env

data RTPointer =
   RTNone
 | NPUnit Int
 | NPBranch Int (Map.Map IRI RTPointer)
        -- here the leaves can be either NPUnit or NPComp
 | NPRef Int Int
 | NPComp (Map.Map IRI RTPointer)
         {- here the leaves can be NPUnit or NPComp
         and roots are needed for inserting edges -}
 deriving (Show, Eq, Ord, Typeable, Data)

-- map nodes

mapRTNodes :: Map.Map Int Int -> RTPointer -> RTPointer
mapRTNodes f rtp = let app = flip $ Map.findWithDefault (error "mapRTNodes")
  in case rtp of
  RTNone -> RTNone
  NPUnit x -> NPUnit (app f x)
  NPRef x y -> NPRef (app f x) (app f y)
  NPBranch x g -> NPBranch (app f x) (Map.map (mapRTNodes f) g)
  NPComp g -> NPComp (Map.map (mapRTNodes f) g)

-- compositions

compPointer :: RTPointer -> RTPointer -> RTPointer
compPointer (NPUnit n1) (NPUnit n2) = NPRef n1 n2
compPointer (NPUnit n1) (NPBranch _ f) = NPBranch n1 f
compPointer (NPUnit n1) (NPRef _ n2) = NPRef n1 n2
compPointer (NPRef n1 _) (NPRef _ n2) = NPRef n1 n2
compPointer (NPRef n1 _) (NPBranch _ f) = NPBranch n1 f
compPointer (NPBranch n1 f1) (NPComp f2) =
       NPBranch n1 (Map.unionWith (\ _ y -> y) f1 f2 )
compPointer (NPComp f1) (NPComp f2) =
       NPComp (Map.unionWith (\ _ y -> y) f1 f2)
compPointer x y = error $ "compPointer:" ++ show x ++ " composed with " ++ show y

-- sources

refSource :: RTPointer -> Int
refSource (NPUnit n) = n
refSource (NPBranch n _) = n
refSource (NPRef n _) = n
refSource x = error ("refSource:" ++ show x)

data RTLeaves = RTLeaf Int | RTLeaves (Map.Map IRI RTLeaves)
 deriving (Show, Typeable, Data)

refTarget :: RTPointer -> RTLeaves
refTarget (NPUnit n) = RTLeaf n
refTarget (NPRef _ n) = RTLeaf n
refTarget (NPComp f) = RTLeaves $ Map.map refTarget f
refTarget (NPBranch _ f) = RTLeaves $ Map.map refTarget f
refTarget x = error ("refTarget:" ++ show x)

-- ** for node names

emptyNodeName :: NodeName
emptyNodeName = NodeName nullIRI "" 0 [] nullRange

showExt :: NodeName -> String
showExt n = let i = extIndex n in extString n ++ if i == 0 then "" else show i

showName :: NodeName -> String
showName n = let ext = showExt n in
    iriToStringShortUnsecure (setAngles False $ getName n)
    ++ if null ext then ext else "__" ++ ext

makeRgName :: IRI -> Range -> NodeName
makeRgName n = NodeName n "" 0 [ElemName $ iriToStringShortUnsecure n]

makeName :: IRI -> NodeName
makeName n = makeRgName n $ iriPos n

setSrcRange :: Range -> NodeName -> NodeName
setSrcRange r n = n { srcRange = r }

parseNodeName :: String -> NodeName
parseNodeName s =
  let err msg = error $ "parseNodeName: malformed NodeName" ++ msg ++ s
      mkName = makeName . fromMaybe (err ": ") . parseCurie
  in case splitByList "__" s of
    [i] -> mkName i
    [i, e] ->
        let n = mkName i
            mSf = numberSuffix e
            (es, sf) = fromMaybe (e, 0) mSf
        in n { extString = es
             , extIndex = sf }
    _ -> err ", too many __: "

incBy :: Int -> NodeName -> NodeName
incBy i n = n
  { extIndex = extIndex n + i
  , xpath = case xpath n of
              ChildIndex j : r -> ChildIndex (j + i) : r
              l -> ChildIndex i : l }

inc :: NodeName -> NodeName
inc = incBy 1

extName :: String -> NodeName -> NodeName
extName s n = n
  { extString = showExt n ++ take 1 s
  , extIndex = 0
  , xpath = ElemName s : xpath n }

-- ** handle edge numbers and proof bases

-- | create a default ID which has to be changed when inserting a certain edge.
defaultEdgeId :: EdgeId
defaultEdgeId = EdgeId $ -1

emptyProofBasis :: ProofBasis
emptyProofBasis = ProofBasis Set.empty

nullProofBasis :: ProofBasis -> Bool
nullProofBasis = Set.null . proofBasis

addEdgeId :: ProofBasis -> EdgeId -> ProofBasis
addEdgeId (ProofBasis s) e = ProofBasis $ Set.insert e s

delEdgeId :: ProofBasis -> EdgeId -> ProofBasis
delEdgeId (ProofBasis s) e = ProofBasis $ Set.delete e s

updEdgeId :: ProofBasis -> EdgeId -> EdgeId -> ProofBasis
updEdgeId pb = addEdgeId . delEdgeId pb

-- | checks if the given edge is contained in the given proof basis..
edgeInProofBasis :: EdgeId -> ProofBasis -> Bool
edgeInProofBasis e = Set.member e . proofBasis

-- * utilities

topsortedLibsWithImports :: Rel.Rel LibName -> [LibName]
topsortedLibsWithImports = concatMap Set.toList . Rel.topSort

getMapAndMaxIndex :: Ord k => k -> (b -> Map.Map k a) -> b -> (Map.Map k a, k)
getMapAndMaxIndex c f gctx =
    let m = f gctx in (m, if Map.null m then c else fst $ Map.findMax m)

-- | or two predicates
liftOr :: (a -> Bool) -> (a -> Bool) -> a -> Bool
liftOr f g x = f x || g x
