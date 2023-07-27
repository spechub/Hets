{-# LANGUAGE ExistentialQuantification, MultiParamTypeClasses
 , DeriveDataTypeable, GeneralizedNewtypeDeriving #-}
{- |
Module      :  ./Logic/Grothendieck.hs
Description :  Grothendieck logic (flattening of logic graph to a single logic)
Copyright   :  (c) Till Mossakowski, and Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (overlapping instances, dynamics, existentials)

Grothendieck logic (flattening of logic graph to a single logic)

The Grothendieck logic is defined to be the
   heterogeneous logic over the logic graph.
   This will be the logic over which the data
   structures and algorithms for specification in-the-large
   are built.

   This module heavily works with existential types, see
   <http://haskell.org/hawiki/ExistentialTypes> and chapter 7 of /Heterogeneous
   specification and the heterogeneous tool set/
   (<http://www.informatik.uni-bremen.de/~till/papers/habil.ps>).

   References:

   R. Diaconescu:
   Grothendieck institutions
   J. applied categorical structures 10, 2002, p. 383-402.

   T. Mossakowski:
   Comorphism-based Grothendieck institutions.
   In K. Diks, W. Rytter (Eds.), Mathematical foundations of computer science,
   LNCS 2420, pp. 593-604

   T. Mossakowski:
   Heterogeneous specification and the heterogeneous tool set.
-}

module Logic.Grothendieck
  ( G_basic_spec (..)
  , G_sign (..)
  , SigId (..)
  , startSigId
  , isHomSubGsign
  , isSubGsign
  , logicOfGsign
  , symsOfGsign
  , G_symbolmap (..)
  , G_mapofsymbol (..)
  , G_symbol (..)
  , G_symb_items_list (..)
  , G_symb_map_items_list (..)
  , G_sublogics (..)
  , isSublogic
  , isProperSublogic
  , joinSublogics
  , G_morphism (..)
  , MorId (..)
  , startMorId
  , mkG_morphism
  , lessSublogicComor
  , LogicGraph (..)
  , setCurLogic
  , setSyntax
  , setCurSublogic
  , emptyLogicGraph
  , lookupLogic
  , lookupCurrentLogic
  , lookupCurrentSyntax
  , lookupCompComorphism
  , lookupComorphism
  , lookupModification
  , GMorphism (..)
  , isHomogeneous
  , Grothendieck (..)
  , gEmbed
  , gEmbed2
  , gEmbedComorphism
  , homGsigDiff
  , gsigUnion
  , gsigManyUnion
  , gsigManyIntersect
  , homogeneousMorManyUnion
  , logicInclusion
  , logicUnion
  , updateMorIndex
  , toG_morphism
  , gSigCoerce
  , ginclusion
  , compInclusion
  , findComorphismPaths
  , logicGraph2Graph
  , findComorphism
  , isTransportable
  , Square (..)
  , LaxTriangle (..)
  , mkIdSquare
  , mkDefSquare
  , mirrorSquare
  , lookupSquare
  ) where

import Logic.Coerce
import Logic.Comorphism
import Logic.ExtSign
import Logic.Logic
import Logic.Modification
import Logic.Morphism

import ATerm.Lib

import Common.Doc
import Common.DocUtils
import Common.ExtSign
import Common.Id
import Common.IRI (IRI)
import Common.Lexer
import Common.Parsec
import Common.Result
import Common.Token
import Common.Utils
import Common.LibName
import Common.GraphAlgo

import Control.Monad (foldM)
import qualified Control.Monad.Fail as Fail
import Data.Maybe
import Data.Typeable
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.HashMap.Strict as HMap
import qualified Data.HashSet as HSet
import qualified Data.Heap as Heap

import Text.Printf

import Text.ParserCombinators.Parsec (Parser, parse, eof, (<|>))
-- for looking up modifications

-- * \"Grothendieck\" versions of the various parts of type class Logic

-- | Grothendieck basic specifications
data G_basic_spec = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
  G_basic_spec lid basic_spec
  deriving Typeable

instance Show G_basic_spec where
    show (G_basic_spec _ s) = show s

instance Pretty G_basic_spec where
    pretty (G_basic_spec _ s) = pretty s

instance GetRange G_basic_spec

-- dummy instances for development graphs
instance Ord G_basic_spec where
  compare _ _ = EQ

instance Eq G_basic_spec where
  _ == _ = True

-- | index for signatures
newtype SigId = SigId Int
  deriving (Typeable, Show, Eq, Ord, Enum, ShATermConvertible)

startSigId :: SigId
startSigId = SigId 0

{- | Grothendieck signatures with an lookup index. Zero indices
 indicate unknown ones. It would be nice to have special (may be
 negative) indices for empty signatures (one for every logic). -}
data G_sign = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree => G_sign
    { gSignLogic :: lid
    , gSign :: ExtSign sign symbol
    , gSignSelfIdx :: SigId -- ^ index to lookup this 'G_sign' in sign map
    } deriving Typeable

instance Eq G_sign where
  a == b = compare a b == EQ

instance Ord G_sign where
  compare (G_sign l1 sigma1 s1) (G_sign l2 sigma2 s2) =
    if s1 > startSigId && s2 > startSigId && s1 == s2 then EQ else
    case compare (Logic l1) $ Logic l2 of
      EQ -> compare (coerceSign l1 l2 "Eq G_sign" sigma1) $ Just sigma2
      r -> r

-- | prefer a faster subsignature test if possible
isHomSubGsign :: G_sign -> G_sign -> Bool
isHomSubGsign (G_sign l1 sigma1 s1) (G_sign l2 sigma2 s2) =
    (s1 > startSigId && s2 > startSigId && s1 == s2) ||
    maybe False (ext_is_subsig l1 sigma1)
      (coerceSign l2 l1 "isHomSubGsign" sigma2)

isSubGsign :: LogicGraph -> G_sign -> G_sign -> Bool
isSubGsign lg (G_sign lid1 (ExtSign sigma1 _) _)
               (G_sign lid2 (ExtSign sigma2 _) _) =
  Just True ==
  do Comorphism cid <- resultToMaybe $
                         logicInclusion lg (Logic lid1) (Logic lid2)
     sigma1' <- coercePlainSign lid1 (sourceLogic cid)
                "Grothendieck.isSubGsign: cannot happen" sigma1
     sigma2' <- coercePlainSign lid2 (targetLogic cid)
                "Grothendieck.isSubGsign: cannot happen" sigma2
     sigma1t <- resultToMaybe $ map_sign cid sigma1'
     return $ is_subsig (targetLogic cid) (fst sigma1t) sigma2'

instance Show G_sign where
    show (G_sign _ s _) = show s

instance Pretty G_sign where
    pretty (G_sign _ (ExtSign s _) _) = pretty s

logicOfGsign :: G_sign -> AnyLogic
logicOfGsign (G_sign lid _ _) = Logic lid

symsOfGsign :: G_sign -> Set.Set G_symbol
symsOfGsign (G_sign lid (ExtSign sgn _) _) = Set.map (G_symbol lid)
    $ symset_of lid sgn

-- | Grothendieck maps with symbol as keys
data G_symbolmap a = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
  G_symbolmap lid (Map.Map symbol a)
  deriving Typeable

instance Show a => Show (G_symbolmap a) where
    show (G_symbolmap _ sm) = show sm

instance (Typeable a, Ord a) => Eq (G_symbolmap a) where
    a == b = compare a b == EQ

instance (Typeable a, Ord a) => Ord (G_symbolmap a) where
  compare (G_symbolmap l1 sm1) (G_symbolmap l2 sm2) =
    case compare (Logic l1) $ Logic l2 of
      EQ -> compare (coerceSymbolmap l1 l2 sm1) sm2
      r -> r


-- | Grothendieck maps with symbol as values
data G_mapofsymbol a = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
  G_mapofsymbol lid (Map.Map a symbol)
  deriving Typeable

instance Show a => Show (G_mapofsymbol a) where
    show (G_mapofsymbol _ sm) = show sm

instance (Typeable a, Ord a) => Eq (G_mapofsymbol a) where
    a == b = compare a b == EQ

instance (Typeable a, Ord a) => Ord (G_mapofsymbol a) where
  compare (G_mapofsymbol l1 sm1) (G_mapofsymbol l2 sm2) =
    case compare (Logic l1) $ Logic l2 of
      EQ -> compare (coerceMapofsymbol l1 l2 sm1) sm2
      r -> r


-- | Grothendieck symbols
data G_symbol = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
  G_symbol lid symbol
  deriving Typeable

instance GetRange G_symbol where
  getRange (G_symbol _ s) = getRange s
  rangeSpan (G_symbol _ s) = rangeSpan s

instance Show G_symbol where
    show (G_symbol _ s) = show s

instance Pretty G_symbol where
    pretty (G_symbol _ s) = pretty s

instance Eq G_symbol where
    a == b = compare a b == EQ

instance Ord G_symbol where
  compare (G_symbol l1 s1) (G_symbol l2 s2) =
    case compare (Logic l1) $ Logic l2 of
      EQ -> compare (coerceSymbol l1 l2 s1) s2
      r -> r

-- | Grothendieck symbol lists
data G_symb_items_list = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
        G_symb_items_list lid [symb_items]
  deriving Typeable

instance GetRange G_symb_items_list

instance Show G_symb_items_list where
    show (G_symb_items_list _ l) = show l

instance Pretty G_symb_items_list where
    pretty (G_symb_items_list _ l) = ppWithCommas l

instance Eq G_symb_items_list where
  (G_symb_items_list i1 s1) == (G_symb_items_list i2 s2) =
     coerceSymbItemsList i1 i2 "Eq G_symb_items_list" s1 == Just s2

-- | Grothendieck symbol maps
data G_symb_map_items_list = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
        G_symb_map_items_list lid [symb_map_items]
  deriving Typeable

instance GetRange G_symb_map_items_list

instance Show G_symb_map_items_list where
    show (G_symb_map_items_list _ l) = show l

instance Pretty G_symb_map_items_list where
    pretty (G_symb_map_items_list _ l) = ppWithCommas l

instance Eq G_symb_map_items_list where
  (G_symb_map_items_list i1 s1) == (G_symb_map_items_list i2 s2) =
     coerceSymbMapItemsList i1 i2 "Eq G_symb_map_items_list" s1 == Just s2

-- | Grothendieck sublogics
data G_sublogics = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
        G_sublogics lid sublogics
  deriving Typeable

instance Show G_sublogics where
    show (G_sublogics lid sub) = language_name lid ++ case sublogicName sub of
      [] -> ""
      h -> '.' : h

instance Eq G_sublogics where
    g1 == g2 = compare g1 g2 == EQ

instance Ord G_sublogics where
    compare (G_sublogics lid1 l1) (G_sublogics lid2 l2) =
      case compare (Logic lid1) $ Logic lid2 of
        EQ -> compare (forceCoerceSublogic lid1 lid2 l1) l2
        r -> r

isSublogic :: G_sublogics -> G_sublogics -> Bool
isSublogic (G_sublogics lid1 l1) (G_sublogics lid2 l2) =
    isSubElem (forceCoerceSublogic lid1 lid2 l1) l2

isProperSublogic :: G_sublogics -> G_sublogics -> Bool
isProperSublogic a b = isSublogic a b && a /= b

joinSublogics :: G_sublogics -> G_sublogics -> Maybe G_sublogics
joinSublogics (G_sublogics lid1 l1) (G_sublogics lid2 l2) =
    case coerceSublogic lid1 lid2 "coerce Sublogic" l1 of
      Just sl -> Just (G_sublogics lid2 (lub sl l2))
      Nothing -> Nothing

-- | index for morphisms
newtype MorId = MorId Int
  deriving (Typeable, Show, Eq, Ord, Enum, ShATermConvertible)

startMorId :: MorId
startMorId = MorId 0

{- | Homogeneous Grothendieck signature morphisms with indices. For
the domain index it would be nice it showed also the emptiness. -}
data G_morphism = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree => G_morphism
    { gMorphismLogic :: lid
    , gMorphism :: morphism
    , gMorphismSelfIdx :: MorId -- ^ lookup index in morphism map
    } deriving Typeable

instance Show G_morphism where
    show (G_morphism _ m _) = show m

instance Pretty G_morphism where
    pretty (G_morphism _ m _) = pretty m

mkG_morphism :: forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree
  => lid -> morphism -> G_morphism
mkG_morphism l m = G_morphism l m startMorId

-- | check if sublogic fits for comorphism
lessSublogicComor :: G_sublogics -> AnyComorphism -> Bool
lessSublogicComor (G_sublogics lid1 sub1) (Comorphism cid) =
    let lid2 = sourceLogic cid
    in Logic lid2 == Logic lid1
        && isSubElem (forceCoerceSublogic lid1 lid2 sub1) (sourceSublogic cid)

type SublogicBasedTheories = Map.Map IRI (LibName, String)

-- | Logic graph
data LogicGraph = LogicGraph
    { logics :: Map.Map String AnyLogic
    , currentLogic :: String
    , currentSyntax :: Maybe IRI
    , currentSublogic :: Maybe G_sublogics
    , currentTargetBase :: Maybe (LibName, String)
    , sublogicBasedTheories :: Map.Map AnyLogic SublogicBasedTheories
    , comorphisms :: Map.Map String AnyComorphism
    , inclusions :: Map.Map (String, String) AnyComorphism
    , unions :: Map.Map (String, String) (AnyComorphism, AnyComorphism)
    , morphisms :: Map.Map String AnyMorphism
    , modifications :: Map.Map String AnyModification
    , squares :: Map.Map (AnyComorphism, AnyComorphism) [Square]
    , qTATranslations :: Map.Map String AnyComorphism
    , prefixes :: Map.Map String IRI
    , dolOnly :: Bool
    } deriving Show

emptyLogicGraph :: LogicGraph
emptyLogicGraph = LogicGraph
    { logics = Map.empty
    , currentLogic = "CASL"
    , currentSyntax = Nothing
    , currentSublogic = Nothing
    , currentTargetBase = Nothing
    , sublogicBasedTheories = Map.empty
    , comorphisms = Map.empty
    , inclusions = Map.empty
    , unions = Map.empty
    , morphisms = Map.empty
    , modifications = Map.empty
    , squares = Map.empty
    , qTATranslations = Map.empty
    , prefixes = Map.empty
    , dolOnly = False
    }

setCurLogicAux :: String -> LogicGraph -> LogicGraph
setCurLogicAux s lg = lg { currentLogic = s }

setCurLogic :: String -> LogicGraph -> LogicGraph
setCurLogic s lg = if s == currentLogic lg then
       lg else setSyntaxAux Nothing $ setCurLogicAux s lg

setSyntaxAux :: Maybe IRI -> LogicGraph -> LogicGraph
setSyntaxAux s lg = lg { currentSyntax = s }

setSyntax :: Maybe IRI -> LogicGraph -> LogicGraph
setSyntax s lg = if isNothing s then lg else setSyntaxAux s lg

setCurSublogic :: Maybe G_sublogics -> LogicGraph -> LogicGraph
setCurSublogic s lg = lg { currentSublogic = s }

instance Pretty LogicGraph where
    pretty lg = text ("current logic is: " ++ currentLogic lg)
       $+$ text "all logics:"
       $+$ sepByCommas (map text $ Map.keys $ logics lg)
       $+$ text "comorphism inclusions:"
       $+$ vcat (map pretty $ Map.elems $ inclusions lg)
       $+$ text "all comorphisms:"
       $+$ vcat (map pretty $ Map.elems $ comorphisms lg)

-- | find a logic in a logic graph
lookupLogic :: Fail.MonadFail m => String -> String -> LogicGraph -> m AnyLogic
lookupLogic error_prefix logname logicGraph =
    case Map.lookup logname $ logics logicGraph of
    Nothing -> Fail.fail $ error_prefix ++ "unknown logic: " ++ logname
    Just lid -> return lid

lookupCurrentLogic :: Fail.MonadFail m => String -> LogicGraph -> m AnyLogic
lookupCurrentLogic msg lg = lookupLogic (msg ++ " ") (currentLogic lg) lg

lookupCurrentSyntax :: Fail.MonadFail m => String -> LogicGraph
  -> m (AnyLogic, Maybe IRI)
lookupCurrentSyntax msg lg = do
  l <- lookupLogic (msg ++ " ") (currentLogic lg) lg
  return (l, currentSyntax lg)

-- | union to two logics
logicUnion :: LogicGraph -> AnyLogic -> AnyLogic
           -> Result (AnyComorphism, AnyComorphism)
logicUnion lg l1@(Logic lid1) l2@(Logic lid2) =
  case logicInclusion lg l1 l2 of
    Result _ (Just c) -> return (c, idComorphism l2)
    _ -> case logicInclusion lg l2 l1 of
      Result _ (Just c) -> return (idComorphism l1, c)
      _ -> case Map.lookup (ln1, ln2) (unions lg) of
        Just u -> return u
        Nothing -> case Map.lookup (ln2, ln1) (unions lg) of
          Just (c2, c1) -> return (c1, c2)
          Nothing -> Fail.fail $ "Union of logics " ++ ln1 ++
                     " and " ++ ln2 ++ " does not exist"
   where ln1 = language_name lid1
         ln2 = language_name lid2

-- | find a comorphism composition in a logic graph
lookupCompComorphism :: Fail.MonadFail m => [String] -> LogicGraph -> m AnyComorphism
lookupCompComorphism nameList logicGraph = do
  cs <- mapM lookupN nameList
  case cs of
    c : cs1 -> foldM compComorphism c cs1
    _ -> Fail.fail "Illegal empty comorphism composition"
  where
  lookupN name =
    case name of
      'i' : 'd' : '_' : logic -> do
         let (mainLogic, subLogicD) = span (/= '.') logic
          -- subLogicD will begin with a . which has to be removed
             msublogic = if null subLogicD
                     then Nothing
                     else Just $ tail subLogicD
         Logic lid <- maybe (Fail.fail ("Cannot find Logic " ++ mainLogic)) return
                 $ Map.lookup mainLogic (logics logicGraph)
         case maybe (Just $ top_sublogic lid) (parseSublogic lid) msublogic of
           Nothing -> Fail.fail $ maybe "missing sublogic"
                    ("unknown sublogic name " ++) msublogic
           Just s -> return $ Comorphism $ mkIdComorphism lid s
      _ -> maybe (Fail.fail ("Cannot find logic comorphism " ++ name)) return
             $ Map.lookup name (comorphisms logicGraph)

-- | find a comorphism in a logic graph
lookupComorphism :: Fail.MonadFail m => String -> LogicGraph -> m AnyComorphism
lookupComorphism = lookupCompComorphism . splitOn ';'

-- | find a modification in a logic graph
lookupModification :: (Fail.MonadFail m) => String -> LogicGraph -> m AnyModification
lookupModification input lG
        = case parse (parseModif lG << eof) "" input of
            Left err -> Fail.fail $ show err
            Right x -> x

parseModif :: (Fail.MonadFail m) => LogicGraph -> Parser (m AnyModification)
parseModif lG = do
  (xs, _) <- separatedBy (vertcomp lG) crossT
  let r = do
        y <- sequence xs
        case y of
          m : ms -> return $ foldM horCompModification m ms
          _ -> Nothing
  case r of
    Nothing -> Fail.fail "Illegal empty horizontal composition"
    Just m -> return m

vertcomp :: (Fail.MonadFail m) => LogicGraph -> Parser (m AnyModification)
vertcomp lG = do
  (xs, _) <- separatedBy (pm lG) semiT
  let r = do
        y <- sequence xs
        case y of
          m : ms -> return $ foldM vertCompModification m ms
          _ -> Nothing
             -- r has type Maybe (m AnyModification)
  case r of
    Nothing -> Fail.fail "Illegal empty vertical composition"
    Just m -> return m

pm :: (Fail.MonadFail m) => LogicGraph -> Parser (m AnyModification)
pm lG = parseName lG <|> bracks lG

bracks :: (Fail.MonadFail m) => LogicGraph -> Parser (m AnyModification)
bracks lG = do
  oParenT
  modif <- parseModif lG
  cParenT
  return modif

parseIdentity :: (Fail.MonadFail m) => LogicGraph -> Parser (m AnyModification)
parseIdentity lG = do
  tryString "id_"
  tok <- simpleId
  let name = tokStr tok
  case Map.lookup name (comorphisms lG) of
    Nothing -> Fail.fail $ "Cannot find comorphism" ++ name
    Just x -> return $ return $ idModification x

parseName :: (Fail.MonadFail m) => LogicGraph -> Parser (m AnyModification)
parseName lG = parseIdentity lG <|> do
  tok <- simpleId
  let name = tokStr tok
  case Map.lookup name (modifications lG) of
    Nothing -> Fail.fail $ "Cannot find modification" ++ name
    Just x -> return $ return x

-- * The Grothendieck signature category

-- | Grothendieck signature morphisms with indices
data GMorphism = forall cid lid1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        sign1 morphism1 symbol1 raw_symbol1 proof_tree1
        lid2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2
        sign2 morphism2 symbol2 raw_symbol2 proof_tree2 .
      Comorphism cid
        lid1 sublogics1 basic_spec1 sentence1
        symb_items1 symb_map_items1
        sign1 morphism1 symbol1 raw_symbol1 proof_tree1
        lid2 sublogics2 basic_spec2 sentence2
        symb_items2 symb_map_items2
        sign2 morphism2 symbol2 raw_symbol2 proof_tree2 => GMorphism
    { gMorphismComor :: cid
    , gMorphismSign :: ExtSign sign1 symbol1
    , gMorphismSignIdx :: SigId -- ^ 'G_sign' index of source signature
    , gMorphismMor :: morphism2
    , gMorphismMorIdx :: MorId  -- ^ `G_morphism index of target morphism
    } deriving Typeable

instance Eq GMorphism where
    a == b = compare a b == EQ

instance Ord GMorphism where
  compare (GMorphism cid1 sigma1 in1 mor1 in1')
    (GMorphism cid2 sigma2 in2 mor2 in2') =
      case compare (Comorphism cid1, G_sign (sourceLogic cid1) sigma1 in1)
            (Comorphism cid2, G_sign (sourceLogic cid2) sigma2 in2) of
        EQ -> if in1' > startMorId && in2' > startMorId && in1' == in2'
          then EQ else
          compare (coerceMorphism (targetLogic cid1) (targetLogic cid2)
                   "Ord GMorphism.coerceMorphism" mor1) (Just mor2)
          -- this coersion will succeed, because cid1 and cid2 are equal
        r -> r

isHomogeneous :: GMorphism -> Bool
isHomogeneous (GMorphism cid _ _ _ _) =
  isIdComorphism (Comorphism cid)

data Grothendieck = Grothendieck deriving (Typeable, Show)

instance Language Grothendieck

instance Show GMorphism where
    show (GMorphism cid s _ m _) =
      show (Comorphism cid) ++ "(" ++ show s ++ ")" ++ show m

instance Pretty GMorphism where
    pretty (GMorphism cid (ExtSign s _) _ m _) = let c = Comorphism cid in fsep
      [ text $ show c
      , if isIdComorphism c then empty else specBraces $ space <> pretty s
      , pretty m ]

-- signature category of the Grothendieck institution
instance Category G_sign GMorphism where
  ide (G_sign lid sigma@(ExtSign s _) ind) =
    GMorphism (mkIdComorphism lid (top_sublogic lid))
              sigma ind (ide s) startMorId
  -- composition of Grothendieck signature morphisms
  composeMorphisms (GMorphism r1 sigma1 ind1 mor1 _)
       (GMorphism r2 _sigma2 _ mor2 _) =
    do let lid1 = sourceLogic r1
           lid2 = targetLogic r1
           lid3 = sourceLogic r2
           lid4 = targetLogic r2
       -- if the second comorphism is the identity then simplify immediately
       if isIdComorphism (Comorphism r2) then do
           mor2' <- coerceMorphism lid4 lid2 "Grothendieck.comp" mor2
           mor' <- composeMorphisms mor1 mor2'
           return (GMorphism r1 sigma1 ind1 mor' startMorId)
         else do
         {- coercion between target of first and
         source of second Grothendieck morphism -}
         mor1' <- coerceMorphism lid2 lid3 "Grothendieck.comp" mor1
         {- map signature morphism component of first Grothendieck morphism
         along the comorphism component of the second one ... -}
         mor1'' <- map_morphism r2 mor1'
         {- and then compose the result with the signature morphism component
         of first one -}
         mor <- composeMorphisms mor1'' mor2
         -- also if the first comorphism is the identity...
         if isIdComorphism (Comorphism r1) &&
           case coerceSublogic lid2 lid3 "Grothendieck.comp"
                              (targetSublogic r1) of
             Just sl1 -> maybe False
                              (isSubElem (targetSublogic r2))
                              (mapSublogic r2 sl1)
             _ -> False
               -- ... then things simplify ...
           then do
             sigma1' <- coerceSign lid1 lid3 "Grothendieck.comp" sigma1
             return (GMorphism r2 sigma1' ind1 mor startMorId)
           else return $ GMorphism (CompComorphism r1 r2)
                sigma1 ind1 mor startMorId
  dom (GMorphism r sigma ind _mor _) =
    G_sign (sourceLogic r) sigma ind
  cod (GMorphism r (ExtSign _ _) _ mor _) =
    let lid2 = targetLogic r
        sig2 = cod mor
    in G_sign lid2 (makeExtSign lid2 sig2) startSigId
  isInclusion (GMorphism cid _ _ mor _) =
    isInclusionComorphism cid && isInclusion mor
  legal_mor (GMorphism r (ExtSign s _) _ mor _) = do
    legal_mor mor
    case maybeResult $ map_sign r s of
      Just (sigma', _) | sigma' == cod mor -> return ()
      _ -> Fail.fail "legal_mor.GMorphism2"

-- | Embedding of homogeneous signature morphisms as Grothendieck sig mors
gEmbed2 :: G_sign -> G_morphism -> GMorphism
gEmbed2 (G_sign lid2 sig si) (G_morphism lid mor ind) =
  let cid = mkIdComorphism lid (top_sublogic lid)
      Just sig1 = coerceSign lid2 (sourceLogic cid) "gEmbed2" sig
  in GMorphism cid sig1 si mor ind

-- | Embedding of homogeneous signature morphisms as Grothendieck sig mors
gEmbed :: G_morphism -> GMorphism
gEmbed (G_morphism lid mor ind) = let sig = dom mor in
  GMorphism (mkIdComorphism lid (top_sublogic lid))
                (makeExtSign lid sig) startSigId mor ind

-- | Embedding of comorphisms as Grothendieck sig mors
gEmbedComorphism :: AnyComorphism -> G_sign -> Result GMorphism
gEmbedComorphism (Comorphism cid) (G_sign lid sig ind) = do
  sig'@(ExtSign s _) <- coerceSign lid (sourceLogic cid) "gEmbedComorphism" sig
  (sigTar, _) <- map_sign cid s
  return (GMorphism cid sig' ind (ide sigTar) startMorId)

-- | heterogeneous union of two Grothendieck signatures
gsigUnion :: LogicGraph -> Bool -> G_sign -> G_sign -> Result G_sign
gsigUnion lg both gsig1@(G_sign lid1 (ExtSign sigma1 _) _)
          gsig2@(G_sign lid2 (ExtSign sigma2 _) _) =
 if Logic lid1 == Logic lid2
    then homogeneousGsigUnion both gsig1 gsig2
    else do
      (Comorphism cid1, Comorphism cid2) <-
            logicUnion lg (Logic lid1) (Logic lid2)
      let lidS1 = sourceLogic cid1
          lidS2 = sourceLogic cid2
          lidT1 = targetLogic cid1
          lidT2 = targetLogic cid2
      sigma1' <- coercePlainSign lid1 lidS1 "Union of signaturesa" sigma1
      sigma2' <- coercePlainSign lid2 lidS2 "Union of signaturesb" sigma2
      (sigma1'', _) <- map_sign cid1 sigma1'  -- where to put axioms???
      (sigma2'', _) <- map_sign cid2 sigma2'  -- where to put axioms???
      sigma2''' <- coercePlainSign lidT2 lidT1 "Union of signaturesc" sigma2''
      sigma3 <- signature_union lidT1 sigma1'' sigma2'''
      return $ G_sign lidT1 (ExtSign sigma3 $ symset_of lidT1
                            $ if both then sigma3 else sigma2''') startSigId

-- | homogeneous Union of two Grothendieck signatures
homogeneousGsigUnion :: Bool -> G_sign -> G_sign -> Result G_sign
homogeneousGsigUnion both (G_sign lid1 sigma1 _) (G_sign lid2 sigma2 _) = do
  sigma2'@(ExtSign sig2 _) <- coerceSign lid2 lid1 "Union of signatures" sigma2
  sigma3@(ExtSign sig3 _) <- ext_signature_union lid1 sigma1 sigma2'
  return $ G_sign lid1
             (if both then sigma3 else ExtSign sig3 $ symset_of lid1 sig2)
         startSigId

homGsigDiff :: G_sign -> G_sign -> Result G_sign
homGsigDiff (G_sign lid1 (ExtSign s1 _) _) (G_sign lid2 (ExtSign s2 _) _) = do
  s3 <- coercePlainSign lid2 lid1 "hom differerence of signatures" s2
  s4 <- signatureDiff lid1 s1 s3
  return $ G_sign lid1 (makeExtSign lid1 s4) startSigId

-- | union of a list of Grothendieck signatures
gsigManyUnion :: LogicGraph -> [G_sign] -> Result G_sign
gsigManyUnion _ [] =
  Fail.fail "union of emtpy list of signatures"
gsigManyUnion lg (gsigma : gsigmas) =
  foldM (gsigUnion lg True) gsigma gsigmas

-- | homogeneous Union of a list of morphisms
homogeneousMorManyUnion :: [G_morphism] -> Result G_morphism
homogeneousMorManyUnion [] =
  Fail.fail "homogeneous union of emtpy list of morphisms"
homogeneousMorManyUnion (gmor : gmors) =
  foldM ( \ (G_morphism lid2 mor2 _) (G_morphism lid1 mor1 _) -> do
            mor1' <- coerceMorphism lid1 lid2 "homogeneousMorManyUnion" mor1
            mor <- morphism_union lid2 mor1' mor2
            return (G_morphism lid2 mor startMorId)) gmor gmors

-- | intersection of a list of Grothendieck signatures
gsigManyIntersect :: LogicGraph -> [G_sign] -> Result G_sign
gsigManyIntersect _ [] =
  Fail.fail "intersection of emtpy list of signatures"
gsigManyIntersect lg (gsigma : gsigmas) =
  foldM (gsigIntersect lg True) gsigma gsigmas

-- | heterogeneous union of two Grothendieck signatures
gsigIntersect :: LogicGraph -> Bool -> G_sign -> G_sign -> Result G_sign
gsigIntersect _lg both gsig1@(G_sign lid1 (ExtSign _sigma1 _) _)
          gsig2@(G_sign lid2 (ExtSign _sigma2 _) _) =
 if Logic lid1 == Logic lid2
    then homogeneousGsigIntersect both gsig1 gsig2
    else error "intersection of heterogeneous signatures is not supported yet"

-- | homogeneous intersection of two Grothendieck signatures
homogeneousGsigIntersect :: Bool -> G_sign -> G_sign -> Result G_sign
homogeneousGsigIntersect _both (G_sign lid1 sigma1@(ExtSign _sig1 syms1) _) (G_sign lid2 sigma2 _) = do
  sigma2'@(ExtSign sig2 _) <- coerceSign lid2 lid1 "Intersection of signatures" sigma2
  ExtSign sig3 _ <- ext_signature_intersect lid1 sigma1 sigma2'
  let syms2 = symset_of lid1 sig2
      symI = Set.intersection syms1 syms2
  return $ G_sign lid1
             (ExtSign sig3 symI)
         startSigId

-- | inclusion between two logics
logicInclusion :: LogicGraph -> AnyLogic -> AnyLogic -> Result AnyComorphism
logicInclusion logicGraph l1@(Logic lid1) (Logic lid2) =
     let ln1 = language_name lid1
         ln2 = language_name lid2 in
     if ln1 == ln2 then
       return (idComorphism l1)
      else case Map.lookup (ln1, ln2) (inclusions logicGraph) of
           Just (Comorphism i) ->
               return (Comorphism i)
           Nothing ->
               Fail.fail ("No inclusion from " ++ ln1 ++ " to " ++ ln2 ++ " found")

updateMorIndex :: MorId -> GMorphism -> GMorphism
updateMorIndex i (GMorphism cid sign si mor _) = GMorphism cid sign si mor i

toG_morphism :: GMorphism -> G_morphism
toG_morphism (GMorphism cid _ _ mor i) = G_morphism (targetLogic cid) mor i

gSigCoerce :: LogicGraph -> G_sign -> AnyLogic
           -> Result (G_sign, AnyComorphism)
gSigCoerce lg g@(G_sign lid1 sigma1 _) l2@(Logic lid2) =
  if Logic lid1 == Logic lid2
    then return (g, idComorphism l2) else do
    cmor@(Comorphism i) <- logicInclusion lg (Logic lid1) l2
    ExtSign sigma1' sy <-
        coerceSign lid1 (sourceLogic i) "gSigCoerce of signature" sigma1
    (sigma1'', _) <- map_sign i sigma1'
    sys <- return . Set.unions . map (map_symbol i sigma1') $ Set.toList sy
    let lid = targetLogic i
    return (G_sign lid (ExtSign sigma1'' sys) startSigId, cmor)

-- | inclusion morphism between two Grothendieck signatures
ginclusion :: LogicGraph -> G_sign -> G_sign -> Result GMorphism
ginclusion = inclusionAux True

inclusionAux :: Bool -> LogicGraph -> G_sign -> G_sign -> Result GMorphism
inclusionAux guard lg (G_sign lid1 sigma1 ind) (G_sign lid2 sigma2 _) = do
    Comorphism i <- logicInclusion lg (Logic lid1) (Logic lid2)
    ext1@(ExtSign sigma1' _) <-
        coerceSign lid1 (sourceLogic i) "Inclusion of signatures" sigma1
    (sigma1'', _) <- map_sign i sigma1'
    ExtSign sigma2' _ <-
        coerceSign lid2 (targetLogic i) "Inclusion of signatures" sigma2
    mor <- (if guard then inclusion else subsig_inclusion)
        (targetLogic i) sigma1'' sigma2'
    return (GMorphism i ext1 ind mor startMorId)

genCompInclusion :: (G_sign -> G_sign -> Result GMorphism)
                 -> GMorphism -> GMorphism -> Result GMorphism
genCompInclusion f mor1 mor2 = do
  let sigma1 = cod mor1
      sigma2 = dom mor2
  incl <- f sigma1 sigma2
  mor <- composeMorphisms mor1 incl
  composeMorphisms mor mor2

{- | Composition of two Grothendieck signature morphisms
with intermediate inclusion -}
compInclusion :: LogicGraph -> GMorphism -> GMorphism -> Result GMorphism
compInclusion = genCompInclusion . inclusionAux False

-- | Find compositions of comorphisms starting from a give logic
-- | use wheted graph of logics to optimize search
findComorphismPaths :: LogicGraph -> G_sublogics -> [AnyComorphism]
findComorphismPaths lg gsubl = nubOrd $ findComorphismCompositions lg gsubl

-- | graph representation of the logic graph
logicGraph2Graph :: LogicGraph
                    -> Graph (G_sublogics, Maybe AnyComorphism) AnyComorphism
logicGraph2Graph lg =
 let relevantMorphisms = filter (\x -> hasModelExpansion x && isRps x && isEps x) . Map.elems 
                         $ comorphisms lg
 in Graph {
  neighbours = \ (G_sublogics lid sl, c1) ->
  let coerce c = forceCoerceSublogic lid (sourceLogic c)
  in Data.Maybe.mapMaybe
      (\ (Comorphism c) -> maybe Nothing (\ sl1 -> Just (Comorphism c,
       (G_sublogics (targetLogic c) sl1, Just $ Comorphism c)))
                (mapSublogic c (coerce c sl))) $
      filter (\ (Comorphism c) -> Logic (sourceLogic c) == Logic lid
      && isSubElem (coerce c sl) (sourceSublogic c)
      && (case c1 of
            Just (Comorphism c1') -> show c1' /= show c
            _ -> True)) relevantMorphisms,
  weight = \ (Comorphism c) -> if Logic (sourceLogic c) ==
                                 Logic (targetLogic c) then 1 else 3
 }

-- | finds first comorphism with a matching sublogic
findComorphism :: Fail.MonadFail m => G_sublogics -> [AnyComorphism] -> m AnyComorphism
findComorphism _ [] = Fail.fail "No matching comorphism found"
findComorphism gsl@(G_sublogics lid sub) (Comorphism cid : rest) =
    let l2 = sourceLogic cid in
    if Logic lid == Logic l2
      && isSubElem (forceCoerceSublogic lid l2 sub) (sourceSublogic cid)
    then return $ Comorphism cid
    else findComorphism gsl rest

{- | check transportability of Grothendieck signature morphisms
(currently returns false for heterogeneous morphisms) -}
isTransportable :: GMorphism -> Bool
isTransportable (GMorphism cid _ ind1 mor ind2) =
    ind1 > startSigId && ind2 > startMorId
    && isModelTransportable (Comorphism cid)
    && is_transportable (targetLogic cid) mor

-- * Lax triangles and weakly amalgamable squares of lax triangles

{- a lax triangle looks like:
            laxTarget
  i -------------------------------------> k
                  ^  laxModif
                 | |
  i ------------- > j -------------------> k
       laxFst              laxSnd

and I_k is quasi-semi-exact -}

data LaxTriangle = LaxTriangle {
                     laxModif :: AnyModification,
                     laxFst, laxSnd, laxTarget :: AnyComorphism
                   } deriving (Show, Eq, Ord)
{- a weakly amalgamable square of lax triangles
consists of two lax triangles with the same laxTarget -}

data Square = Square {
                 leftTriangle, rightTriangle :: LaxTriangle
              } deriving (Show, Eq, Ord)

-- for deriving Eq, first equality for modifications is needed

mkIdSquare :: AnyLogic -> Square
mkIdSquare (Logic lid) = let
   idCom = Comorphism (mkIdComorphism lid (top_sublogic lid))
   idMod = idModification idCom
   idTriangle = LaxTriangle {
                 laxModif = idMod,
                 laxFst = idCom,
                 laxSnd = idCom,
                 laxTarget = idCom}
 in Square {leftTriangle = idTriangle, rightTriangle = idTriangle}

mkDefSquare :: AnyComorphism -> Square
mkDefSquare c1@(Comorphism cid1) = let
  idComS = Comorphism $ mkIdComorphism (sourceLogic cid1) $
           top_sublogic $ sourceLogic cid1
  idComT = Comorphism $ mkIdComorphism (targetLogic cid1) $
           top_sublogic $ targetLogic cid1
  idMod = idModification c1
  lTriangle = LaxTriangle {
               laxModif = idMod,
               laxFst = c1,
               laxSnd = idComS,
               laxTarget = c1
              }
  rTriangle = LaxTriangle {
               laxModif = idMod,
               laxFst = idComT,
               laxSnd = c1,
               laxTarget = c1
              }
 in Square {leftTriangle = lTriangle, rightTriangle = rTriangle}

mirrorSquare :: Square -> Square
mirrorSquare s = Square {
                 leftTriangle = rightTriangle s,
                 rightTriangle = leftTriangle s}

lookupSquare :: AnyComorphism -> AnyComorphism -> LogicGraph -> Result [Square]
lookupSquare com1 com2 lg = maybe (Fail.fail "lookupSquare") return $ do
  sqL1 <- Map.lookup (com1, com2) $ squares lg
  sqL2 <- Map.lookup (com2, com1) $ squares lg
  return $ nubOrd $ sqL1 ++ map mirrorSquare sqL2
  -- maybe adjusted if comparing AnyModifications change

-- | algo for searching comorphism paths
weight_limit :: Int
weight_limit = 4

times_logic_in_branch :: Int
times_logic_in_branch = 3

data SearchNode = SearchNode
  { nodeId :: Int,
    parentId :: Int,
    logicName :: String,
    -- to check wether comorphism already used in branch
    usedComorphisms :: HSet.HashSet String,
    -- number of time particular logic is used in branch
    timesLogicUsed :: HMap.HashMap String Int,
    -- all comorphism composition in current branch, latest one in the head of the list
    cCompositions :: [AnyComorphism],
    -- name of comorphism though wich we get this node from parent
    comName :: String,
    -- weight of comorphism leading to that node
    comWeight :: Int
  }
  deriving (Show)

data SearchState = SearchState
  {
    searchNodes :: HMap.HashMap Int SearchNode,
    -- ids of nodes who are currently leaves in search tree
    leaves :: HSet.HashSet Int,
    -- distances of nodes in priority queues to root node
    distance :: HMap.HashMap Int Int,
    -- priority queue of nodes according their distances: higher distance - higher priority
    pQueue :: Heap.MinPrioHeap Int Int,
    -- map logic map to comorphis with it as source logic
    logicToComorphisms :: HMap.HashMap String [String],
    -- this field = <last node id in searchNodes> + 1.
    -- used for proper id generation of children nodes
    nextNodeId :: Int
  }

initState :: LogicGraph -> G_sublogics -> SearchState
initState lg (G_sublogics lid sub) =
  SearchState
    { leaves = HSet.empty,
      searchNodes =
        HMap.fromList
          [ ( 0,
              SearchNode
                0
                (-1)
                (language_name lid)
                HSet.empty
                HMap.empty
                [Comorphism $ mkIdComorphism lid sub]
                []
                0
            )
          ],
      distance = HMap.fromList [(0, 0)],
      pQueue = Heap.fromList [(0, 0)],
      logicToComorphisms = mapLogicsToComorphisms lg,
      nextNodeId = 1
    }

findComorphismCompositions :: LogicGraph -> G_sublogics -> [AnyComorphism]
findComorphismCompositions lg gsubl =
  processSearchState lg (initState lg gsubl)

processSearchState :: LogicGraph -> SearchState -> [AnyComorphism]
processSearchState lg state@(SearchState ns ls _ pq _ _) = case Heap.view pq of
  Nothing -> getComorphismCompositions ns ls
  Just ((dist, nId), pq') ->
    let curNode =
          fromMaybe
            ( error $
                printf "processSearchState, incorrect nId=%d" nId
            )
            $ HMap.lookup nId ns
        -- remove parent node from global map of nodes
        -- as we don't need it there anymore so GC can utilize
        -- it if required
        ns' = HMap.delete (parentId curNode) ns
        -- remove parent node from set of leaves and put current node there
        ls' = HSet.insert nId $ HSet.delete (parentId curNode) ls
     in processSearchState lg $
          processNeighbours
            lg
            nId
            dist
            ( state
                { searchNodes = ns',
                  leaves = ls',
                  pQueue = pq'
                }
            )

getComorphismCompositions ::
  HMap.HashMap Int SearchNode -> -- nodes of search graph
  HSet.HashSet Int -> -- leaves in this graph
  [AnyComorphism]
getComorphismCompositions sNodes lvs =
  let res =
        concat $
          map
            ( \i ->
                let leaf = HMap.lookup i sNodes
                 in reverse $
                      cCompositions $
                        fromMaybe
                          ( error $
                              printf "getComorphismComositions, incorrect i=%d key for HashMap" i
                          )
                          $ leaf
            )
            $ HSet.toList $ lvs
   in res

getComorphism :: LogicGraph -> String -> AnyComorphism
getComorphism lg cn =
  fromMaybe (error (printf "getComorphism, incorrect comorphismName=%s key for HashMap" cn)) $
    Map.lookup cn (comorphisms lg)

getTargetLogicName :: AnyComorphism -> String
getTargetLogicName (Comorphism cid) = language_name $ targetLogic cid

-- | given node in tree generate candidate nodes and put them in priority queue
processNeighbours :: LogicGraph -> Int -> Int -> SearchState -> SearchState
processNeighbours lg nId dist state@(SearchState ns _ ds pq ltcs nni) =
  let curNode =
        fromMaybe (error $ printf "processNeighbours, incorrect nId=%d key for HashMap" nId) $
          HMap.lookup nId ns
      lName = logicName curNode
      comCandidates = HMap.lookupDefault [] lName ltcs
      comCandidates' = filter (\name -> not $ HSet.member name (usedComorphisms curNode)) comCandidates
      -- create SearchNodes when possible due to restrictions and add ids later
      -- this code can be expressed as map (create_SearchNode) $ filter (can_create_SearchNode?)
      -- but implemented this way without map-filter separation
      childrenNodes =
        catMaybes $
          map
            ( \name ->
                let c = getComorphism lg name
                    targetLogicName = getTargetLogicName c
                    tlu = HMap.lookupDefault 0 targetLogicName (timesLogicUsed curNode)
                    newComposition =
                      compComorphism (head $ cCompositions curNode) c
                    cw = HMap.lookupDefault (maxWeight + 1) name comorphismWeight
                 in if (isJust newComposition && tlu <= times_logic_in_branch && cw + dist <= weight_limit)
                      then
                        Just $
                          SearchNode
                            { nodeId = -1, -- dummy value for now, changed later in processNeighbours
                              parentId = nId,
                              logicName = targetLogicName,
                              usedComorphisms = HSet.insert name (usedComorphisms curNode),
                              timesLogicUsed = HMap.insert targetLogicName (tlu + 1) (timesLogicUsed curNode),
                              cCompositions = (fromJust newComposition) : (cCompositions curNode),
                              comName = name,
                              comWeight = cw
                            }
                      else Nothing
            )
            comCandidates'

      -- add ids to SearchNodes
      (childrenNodes', next_nni) = foldl (\(acc, i) sn -> (sn{ nodeId = i } : acc, i + 1)) ([], nni) childrenNodes

      -- update map of nodes
      ns' = foldl (\_ns sn -> HMap.insert (nodeId sn) sn _ns) ns childrenNodes'
      -- update distances in SearchState
      ds' = foldl (\_ds sn -> HMap.insert (nodeId sn) (dist + comWeight sn) _ds) ds childrenNodes'
      -- update priority queue
      pq' = foldl (\_pq sn -> Heap.insert (dist + comWeight sn, nodeId sn) _pq) pq childrenNodes'
   in state {searchNodes = ns', distance = ds', pQueue = pq', nextNodeId = next_nni}

mapLogicsToComorphisms :: LogicGraph -> HMap.HashMap String [String]
mapLogicsToComorphisms lg =
  foldr
    ( \(cName, Comorphism cId) acc ->
        let sourceLogicName = language_name $ sourceLogic cId
            l = HMap.lookupDefault [] sourceLogicName acc
         in HMap.insert sourceLogicName (cName : l) acc
    )
    HMap.empty
    $ Map.toList $ comorphisms lg

-- | assign weights to comorphisms

maxWeight :: Int
maxWeight = 5

comorphismWeight :: HMap.HashMap String Int
comorphismWeight =
  HMap.fromList
    [ ("CASL2CoCASL", 5),
      ("CASL2CspCASL", 5),
      ("CASL2ExtModal", 5),
      ("CASL2HasCASL", 5),
      ("CASL2Hybrid", 5),
      ("CASL2Modal", 5),
      ("CASL2VSE", 5),
      ("CASL2VSEImport", 5),
      ("CASL2VSERefine", 5),
      ("HasCASL2IsabelleDeprecated", 5),
      ("OWL22NeSyPatterns", 5),
      ("CASL_DL2CASL", 4),
      ("CASL2Propositional", 4),
      ("CASL2OWL", 4),
      ("OWL22CommonLogic", 4),
      ("Propositional2CommonLogic", 4),
      ("Propositional2OWL2", 4),
      ("Propositional2QBF", 4),
      ("SoftFOL2CommonLogic", 4),
      ("THFP_P2HasCASL", 3),
      ("CspCASL2Modal", 3),
      ("OWL22CASL", 2),
      ("Propositional2CASL", 2),
      ("CoCASL2Isabelle", 2),
      ("CommonLogic2Isabelle", 2),
      ("CASL2Isabelle", 2),
      ("CommonLogicModuleElimination", 2),
      ("CspCASL2CspCASL_Failure", 2),
      ("CspCASL2CspCASL_Trace", 2),
      ("HasCASL2IsabelleOption", 2),
      ("THFP2THF0", 2),
      ("THFP_P2THFP", 2),
      ("Adl2CASL", 1),
      ("CASL2NNF", 1),
      ("CASL2PCFOL", 1),
      ("CASL2PCFOLTopSort", 1),
      ("CASL2Prenex", 1),
      ("CASL2Skolem", 1),
      ("CASL2SoftFOL", 1),
      ("CASL2SoftFOLInduction", 1),
      ("CASL2SoftFOLInduction2", 1),
      ("CASL2SubCFOL", 1),
      ("CASL2SubCFOLNoMembershipOrCast", 1),
      ("CASL2SubCFOLSubsortBottoms", 1),
      ("CASL2TPTP_FOF", 1),
      ("CLFol2CFOL", 1),
      ("CLFull2CFOL", 1),
      ("CLImp2CFOL", 1),
      ("CLSeq2CFOL", 1),
      ("CoCASL2CoPCFOL", 1),
      ("CoCASL2CoSubCFOL", 1),
      ("CSMOF2CASL", 1),
      ("DFOL2CASL", 1),
      ("DMU2OWL2", 1),
      ("ExtModal2CASL", 1),
      ("ExtModal2ExtModalNoSubsorts", 1),
      ("ExtModal2ExtModalTotal", 1),
      ("ExtModal2HasCASL", 1),
      ("ExtModal2OWL", 1),
      ("ExtModal2OWL", 1),
      ("HasCASL2HasCASLPrograms", 1),
      ("HasCASL2THFP_P", 1),
      ("HolLight2Isabelle", 1),
      ("Hybrid2CASL", 1),
      ("Maude2CASL", 1),
      ("Modal2CASL", 1),
      ("MonadicTranslation", 1),
      ("NormalisingTranslation", 1),
      ("QBF2Propositional", 1),
      ("QVTR2CASL", 1),
      ("RelScheme2CASL", 1)
    ]
