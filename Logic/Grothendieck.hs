{- |
Module      :  $Header$
Description :  Grothendieck logic (flattening of logic graph to a single logic)
Copyright   :  (c) Till Mossakowski, and Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
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

   Transportability for heterogeneous morphisms -solved
-}

module Logic.Grothendieck(
       G_basic_spec (..)
     , G_sign (..)
     , isHomSubGsign
     , isSubGsign
     , langNameSig
     , G_symbol (..)
     , G_symb_items_list (..)
     , G_symb_map_items_list (..)
     , G_diagram (..)
     , G_sublogics (..)
     , isProperSublogic
     , G_morphism (..)
     , AnyComorphism (..)
     , idComorphism
     , isIdComorphism
     , isInclComorphism
     , isModelTransportable
     , hasModelExpansion
     , isWeaklyAmalgamable
     , compComorphism
     , lessSublogicComor
     , AnyMorphism (..)
     , AnyModification (..)
     , idModification
     , vertCompModification
     , horCompModification
     , LogicGraph (..)
     , emptyLogicGraph
     , HetSublogicGraph (..)
     , emptyHetSublogicGraph
     , lookupLogic
     , lookupCurrentLogic
     , logicUnion
     , lookupCompComorphism
     , lookupComorphism
     , lookupModification
     , GMorphism (..)
     , isHomogeneous
     , Grothendieck (..)
     , normalize
     , gEmbed
     , gEmbed2
     , gEmbedComorphism
     , gsigUnion
     , gsigManyUnion
     , homogeneousMorManyUnion
     , logicInclusion
     , updateMorIndex
     , toG_morphism
     , ginclusion
     , compInclusion
     , compHomInclusion
     , findComorphismPaths
     , findComorphism
     , isTransportable
     , G_prover (..)
     , getProverName
     , coerceProver
     , G_cons_checker (..)
     , coerceConsChecker
     , coerceG_sign
)

 where

import Logic.Logic
import Logic.ExtSign
import Logic.Prover
import Logic.Comorphism
import Logic.Morphism
import Logic.Coerce
import Common.Doc
import Common.DocUtils
import qualified Common.Lib.Graph as Tree
import qualified Data.Map as Map
import Common.Result
import Common.Utils
import Data.Typeable
import Data.List (nub)
import Data.Maybe (catMaybes)
import Control.Monad (foldM, unless)
import Logic.Modification
import Text.ParserCombinators.Parsec (Parser, try, parse, eof, string, (<|>))
-- for looking up modifications
import Common.Token
import Common.Lexer
import Common.Id

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
    , gSign :: (ExtSign sign symbol)
    , gSignSelfIdx :: Int -- ^ index to lookup this 'G_sign' in sign map
    } deriving Typeable

instance Eq G_sign where
  G_sign l1 sigma1 i1 == G_sign l2 sigma2 i2 =
    (i1 > 0 && i2 > 0 && i1 == i2) ||
     coerceSign l1 l2 "Eq G_sign" sigma1 == Just sigma2

-- | prefer a faster subsignature test if possible
isHomSubGsign :: G_sign -> G_sign -> Bool
isHomSubGsign (G_sign i1 sigma1 s1) (G_sign i2 sigma2 s2) =
    if s1 == s2 then True else
    maybe False (ext_is_subsig i1 sigma1)
      $ coerceSign i2 i1 "isHomSubGsign" sigma2

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

langNameSig :: G_sign -> String
langNameSig (G_sign lid _ _) = language_name lid

-- | Grothendieck symbols
data G_symbol = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree  =>
  G_symbol lid symbol
  deriving Typeable

instance Show G_symbol where
    show (G_symbol _ s) = show s

instance Pretty G_symbol where
    pretty (G_symbol _ s) = pretty s

instance Eq G_symbol where
  (G_symbol i1 s1) == (G_symbol i2 s2) =
     language_name i1 == language_name i2 && coerceSymbol i1 i2 s1 == s2

-- | Grothendieck symbol lists
data G_symb_items_list = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree  =>
        G_symb_items_list lid [symb_items]
  deriving Typeable

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
          sign morphism symbol raw_symbol proof_tree  =>
        G_symb_map_items_list lid [symb_map_items]
  deriving Typeable

instance Show G_symb_map_items_list where
    show (G_symb_map_items_list _ l) = show l

instance Pretty G_symb_map_items_list where
    pretty (G_symb_map_items_list _ l) = ppWithCommas l

instance Eq G_symb_map_items_list where
  (G_symb_map_items_list i1 s1) == (G_symb_map_items_list i2 s2) =
     coerceSymbMapItemsList i1 i2 "Eq G_symb_map_items_list" s1 == Just s2

-- | Grothendieck diagrams
data G_diagram = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree  =>
        G_diagram lid (Tree.Gr sign morphism)
  deriving Typeable

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
    show (G_sublogics lid sub) = case sublogic_names sub of
      [] -> error "show G_sublogics"
      h : _ -> show lid ++ (if null h then "" else "." ++ h)

instance Eq G_sublogics where
    g1 == g2 = compare g1 g2 == EQ

instance Ord G_sublogics where
    compare (G_sublogics lid1 l1) (G_sublogics lid2 l2) =
       case compare (language_name lid1) $ language_name lid2 of
         EQ -> compare (forceCoerceSublogic lid1 lid2 l1) l2
         r -> r

isProperSublogic :: G_sublogics -> G_sublogics -> Bool
isProperSublogic a@(G_sublogics lid1 l1) b@(G_sublogics lid2 l2) =
    isSubElem (forceCoerceSublogic lid1 lid2 l1) l2 && a /= b

{- | Homogeneous Grothendieck signature morphisms with indices. For
the domain index it would be nice it showed also the emptiness. -}
data G_morphism = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree => G_morphism
    { gMorphismLogic :: lid
    , gMorphismSelfIdx :: Int -- ^ lookup index in morphism map
    , gMorphism :: morphism
    , gMorphismDomIdx :: Int -- ^ 'G_sign' index of domain
    , gMorphismCodIdx :: Int -- ^ 'G_sign' index of codomain
    } deriving Typeable

instance Show G_morphism where
    show (G_morphism _ _ l _ _) = show l

-- * Comorphisms and existential types for the logic graph

-- | Existential type for comorphisms
data AnyComorphism = forall cid lid1 sublogics1
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
                 sign2 morphism2 symbol2 raw_symbol2 proof_tree2 =>
      Comorphism cid
  deriving Typeable

instance Eq AnyComorphism where
  Comorphism cid1 == Comorphism cid2 =
     constituents cid1 == constituents cid2
  -- need to be refined, using comorphism translations !!!

instance Show AnyComorphism where
  show (Comorphism cid) = language_name cid
    ++ " : " ++ language_name (sourceLogic cid)
    ++ " -> " ++ language_name (targetLogic cid)

-- | compute the identity comorphism for a logic
idComorphism :: AnyLogic -> AnyComorphism
idComorphism (Logic lid) = Comorphism (mkIdComorphism lid (top_sublogic lid))

-- | Test whether a comporphism is the identity
isIdComorphism :: AnyComorphism -> Bool
isIdComorphism (Comorphism cid) =
  constituents cid == []

-- | Test wether a comorphism is an ad-hoc inclusion
isInclComorphism :: AnyComorphism -> Bool
isInclComorphism (Comorphism cid) =
    Logic (sourceLogic cid) == Logic (targetLogic cid) &&
    (isProperSublogic (G_sublogics (sourceLogic cid) (sourceSublogic cid))
                      (G_sublogics (targetLogic cid) (targetSublogic cid)))

-- * Properties of comorphisms

-- | Test whether a comorphism is model-transportable
isModelTransportable :: AnyComorphism -> Bool
isModelTransportable (Comorphism cid) = is_model_transportable cid

-- | Test whether a comorphism has model expansion
hasModelExpansion :: AnyComorphism -> Bool
hasModelExpansion (Comorphism cid) = has_model_expansion cid

-- | Test whether a comorphism is weakly amalgamable
isWeaklyAmalgamable :: AnyComorphism -> Bool
isWeaklyAmalgamable (Comorphism cid) = is_weakly_amalgamable cid

-- | Compose comorphisms
compComorphism :: Monad m => AnyComorphism -> AnyComorphism -> m AnyComorphism
compComorphism (Comorphism cid1) (Comorphism cid2) =
   let l1 = targetLogic cid1
       l2 = sourceLogic cid2 in
   if language_name l1 == language_name l2 then
      if isSubElem (forceCoerceSublogic l1 l2 $ targetSublogic cid1)
            $ sourceSublogic cid2
       then {- case (isIdComorphism cm1,isIdComorphism cm2) of
         (True,_) -> return cm2
         (_,True) -> return cm1
         _ ->  -} return $ Comorphism (CompComorphism cid1 cid2)
       else fail ("Sublogic mismatch in composition of "++language_name cid1++
                  " and "++language_name cid2)
    else fail ("Logic mismatch in composition of "++language_name cid1++
                     " and "++language_name cid2)

-- | check if sublogic fits for comorphism
lessSublogicComor :: G_sublogics -> AnyComorphism -> Bool
lessSublogicComor (G_sublogics lid1 sub1) (Comorphism cid) =
    let lid2 = sourceLogic cid
    in language_name lid2 == language_name lid1
        && isSubElem (forceCoerceSublogic lid1 lid2 sub1) (sourceSublogic cid)

-- * Morphisms

-- | Existential type for morphisms
data AnyMorphism = forall cid lid1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        sign1 morphism1 symbol1 raw_symbol1 proof_tree1
        lid2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2
        sign2 morphism2 symbol2 raw_symbol2 proof_tree2 .
      Morphism cid
                 lid1 sublogics1 basic_spec1 sentence1
                 symb_items1 symb_map_items1
                 sign1 morphism1 symbol1 raw_symbol1 proof_tree1
                 lid2 sublogics2 basic_spec2 sentence2
                 symb_items2 symb_map_items2
                 sign2 morphism2 symbol2 raw_symbol2 proof_tree2 =>
      Morphism cid
  deriving Typeable

{-
instance Eq AnyMorphism where
  Morphism cid1 == Morphism cid2 =
     constituents cid1 == constituents cid2
  -- need to be refined, using morphism translations !!!
-}

instance Show AnyMorphism where
  show (Morphism cid) =
    language_name cid
    ++" : "++language_name (morSourceLogic cid)
    ++" -> "++language_name (morTargetLogic cid)

-- * Modifications

data AnyModification = forall
                     lid cid1 cid2
            log1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            log2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
            log3 sublogics3 basic_spec3 sentence3 symb_items3 symb_map_items3
                sign3 morphism3 symbol3 raw_symbol3 proof_tree3
            log4 sublogics4 basic_spec4 sentence4 symb_items4 symb_map_items4
                sign4 morphism4 symbol4 raw_symbol4 proof_tree4.
                      Modification lid cid1 cid2
            log1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            log2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
            log3 sublogics3 basic_spec3 sentence3 symb_items3 symb_map_items3
                sign3 morphism3 symbol3 raw_symbol3 proof_tree3
            log4 sublogics4 basic_spec4 sentence4 symb_items4 symb_map_items4
                sign4 morphism4 symbol4 raw_symbol4 proof_tree4
            => Modification lid
  deriving Typeable

{--
instance Eq AnyModification where

  find rules for equality

--}

instance Show AnyModification where
   show (Modification lid) = language_name lid ++
                             ":" ++ language_name (sourceComorphism lid) ++
                             "=>" ++ language_name (targetComorphism lid)

idModification :: AnyComorphism -> AnyModification
idModification (Comorphism cid) = Modification (IdModif cid)

-- | vertical compositions of modifications

vertCompModification :: Monad m => AnyModification -> AnyModification
                     -> m AnyModification
vertCompModification (Modification lid1) (Modification lid2) =
   let cid1 = targetComorphism lid1
       cid2 = sourceComorphism lid2
   in
    if language_name cid1 == language_name cid2
    then return $ Modification (VerCompModif lid1 lid2)
    else fail $ "Comorphism mismatch in composition of" ++ language_name lid1
             ++ "and" ++  language_name lid2

-- | horizontal composition of modifications

horCompModification :: Monad m => AnyModification -> AnyModification
                    -> m AnyModification
horCompModification (Modification lid1) (Modification lid2) =
   let cid1 = sourceComorphism lid1
       cid2 = sourceComorphism lid2
   in if language_name (targetLogic cid1) == language_name (sourceLogic cid2)
      then return $ Modification (HorCompModif lid1 lid2)
      else fail $ "Logic mismatch in composition of" ++ language_name lid1
               ++ "and" ++ language_name lid2

-- | Logic graph
data LogicGraph = LogicGraph
    { logics :: Map.Map String AnyLogic
    , currentLogic :: String
    , comorphisms :: Map.Map String AnyComorphism
    , inclusions :: Map.Map (String, String) AnyComorphism
    , unions :: Map.Map (String, String) (AnyComorphism, AnyComorphism)
    , morphisms :: Map.Map String AnyMorphism
    , modifications :: Map.Map String AnyModification }

emptyLogicGraph :: LogicGraph
emptyLogicGraph = LogicGraph
    { logics = Map.empty
    , currentLogic = "CASL"
    , comorphisms = Map.empty
    , inclusions = Map.empty
    , unions = Map.empty
    , morphisms = Map.empty
    , modifications = Map.empty }

-- | Heterogenous Sublogic Graph
-- this graph only contains interesting Sublogics plus comorphisms relating
-- these sublogics; a comorphism might be mentioned multiple times
data HetSublogicGraph = HetSublogicGraph
    { sublogicNodes :: Map.Map String G_sublogics
    , comorphismEdges :: Map.Map (String,String) [AnyComorphism]}

emptyHetSublogicGraph :: HetSublogicGraph
emptyHetSublogicGraph = HetSublogicGraph Map.empty Map.empty

-- | find a logic in a logic graph
lookupLogic :: Monad m => String -> String -> LogicGraph -> m AnyLogic
lookupLogic error_prefix logname logicGraph =
    case Map.lookup logname $ logics logicGraph of
    Nothing -> fail $ error_prefix ++" in LogicGraph logic \""
                      ++ logname ++ "\" unknown"
    Just lid -> return lid

lookupCurrentLogic :: Monad m => String -> LogicGraph -> m AnyLogic
lookupCurrentLogic msg lg = lookupLogic msg (currentLogic lg) lg

-- | union to two logics
logicUnion :: LogicGraph -> AnyLogic -> AnyLogic
           -> Result (AnyComorphism, AnyComorphism)
logicUnion lg l1@(Logic lid1) l2@(Logic lid2) =
  case logicInclusion lg l1 l2 of
    Result _ (Just c) -> return (c,idComorphism l2)
    _ -> case logicInclusion lg l2 l1 of
      Result _ (Just c) -> return (idComorphism l1,c)
      _ -> case Map.lookup (ln1,ln2) (unions lg) of
        Just u -> return u
        Nothing -> case Map.lookup (ln2,ln1) (unions lg) of
          Just (c2,c1) -> return (c1,c2)
          Nothing -> fail $ "Union of logics " ++ ln1 ++
                     " and " ++ ln2 ++ " does not exist"
   where ln1 = language_name lid1
         ln2 = language_name lid2

-- | find a comorphism composition in a logic graph
lookupCompComorphism :: Monad m => [String] -> LogicGraph -> m AnyComorphism
lookupCompComorphism nameList logicGraph = do
  cs <- sequence $ map lookupN nameList
  case cs of
    c:cs1 -> foldM compComorphism c cs1
    _ -> fail "Illegal empty comorphism composition"
  where
  hasSublogic name (Logic lid) = elem name (sublogic_names $ top_sublogic lid)
  lookupN name =
    case name of
      'i':'d':'_':logic -> do
         let (mainLogic, subLogicD) = span (/= '.') logic
          --subLogicD will begin with a . which has to be removed
         l <- maybe (fail ("Cannot find Logic "++mainLogic)) return
                 $ Map.lookup mainLogic (logics logicGraph)
         case hasSublogic (tail subLogicD) l of
           True ->  return $ idComorphism l
           False -> fail ("Error in sublogic name"++logic)
      _ -> maybe (fail ("Cannot find logic comorphism "++name)) return
             $ Map.lookup name (comorphisms logicGraph)
-- | find a comorphism in a logic graph
lookupComorphism :: Monad m => String -> LogicGraph -> m AnyComorphism
lookupComorphism coname = lookupCompComorphism $ splitOn ';' coname

-- | find a modification in a logic graph
lookupModification :: (Monad m) => String -> LogicGraph -> m AnyModification
lookupModification input lG
        = case parse (parseModif lG << eof) "" input of
            Left err -> fail $ show err
            Right x  -> x

parseModif :: (Monad m) => LogicGraph -> Parser (m AnyModification)
parseModif lG = do
             (xs, _) <- separatedBy (vertcomp lG) crossT
             let r = do  y <- sequence xs
                         case y of
                           m:ms -> return $ foldM horCompModification m ms
                           _ -> Nothing
             case r of
               Nothing -> fail "Illegal empty horizontal composition"
               Just m -> return m

vertcomp :: (Monad m) => LogicGraph -> Parser (m AnyModification)
vertcomp lG = do
             (xs, _) <- separatedBy (pm lG) semiT
             let r = do
                      y <- sequence xs
                      case y of
                       m:ms -> return $ foldM vertCompModification m ms
                       _  -> Nothing
             --r has type Maybe (m AnyModification)
             case r of
               Nothing -> fail "Illegal empty vertical composition"
               Just m -> return m

pm :: (Monad m) => LogicGraph -> Parser (m AnyModification)
pm lG = parseName lG <|> bracks lG

bracks :: (Monad m) => LogicGraph -> Parser (m AnyModification)
bracks lG = do
  oParenT
  modif <- parseModif lG
  cParenT
  return modif

parseIdentity :: (Monad m) => LogicGraph -> Parser (m AnyModification)
parseIdentity lG = do
  try (string "id_")
  tok <- simpleId
  let name = tokStr tok
  case Map.lookup name (comorphisms lG) of
    Nothing -> fail $ "Cannot find comorphism" ++ name
    Just x -> return $ return $ idModification x

parseName :: (Monad m) => LogicGraph -> Parser (m AnyModification)
parseName lG = parseIdentity lG <|> do
  tok <- simpleId
  let name = tokStr tok
  case Map.lookup name (modifications lG) of
    Nothing -> fail $ "Cannot find modification" ++ name
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
    , gMorphismSignIdx :: Int -- ^ 'G_sign' index of source signature
    , gMorphismMor :: morphism2
    , gMorphismMorIdx :: Int  -- ^ `G_morphism index of target morphism
    } deriving Typeable

instance Eq GMorphism where
  GMorphism cid1 sigma1 in1 mor1 in1' == GMorphism cid2 sigma2 in2 mor2 in2'
     = Comorphism cid1 == Comorphism cid2
       && G_sign (sourceLogic cid1) sigma1 in1 ==
          G_sign (sourceLogic cid2) sigma2 in2
       && (in1' > 0 && in2' > 0 && in1' == in2'
          || coerceMorphism (targetLogic cid1) (targetLogic cid2)
                   "Eq GMorphism.coerceMorphism" mor1 == Just mor2)

isHomogeneous :: GMorphism -> Bool
isHomogeneous (GMorphism cid _ _ _ _) =
  isIdComorphism (Comorphism cid)

data Grothendieck = Grothendieck deriving (Typeable, Show)

instance Language Grothendieck

instance Show GMorphism where
    show (GMorphism cid s _ m _) =
      show (normalize (Comorphism cid)) ++ "(" ++ show s ++ ")" ++ show m

instance Pretty GMorphism where
    pretty (GMorphism cid (ExtSign s _) _ m _) =
      text (show (normalize (Comorphism cid)))
      <+>
      parens (space <> pretty s <> space)
      $+$
      pretty m

normalize :: AnyComorphism -> AnyComorphism
normalize = id
{- todo: somthing like the following...
normalize (Comorphism cid) =
  case cid of
   CompComorphism r1 r2 ->
    case (normalize (Comorphism r1),  normalize (Comorphism r2)) of
     (Comorphism n1, Comorphism n2) ->
       if isIdComorphism (Comorphism n1) then Comorphism n2
         else if isIdComorphism (Comorphism n2) then Comorphism n1
           else Comorphism (CompComorphism n1 n2)
   _ -> Comorphism cid
-}

instance Category Grothendieck G_sign GMorphism where
  ide _ (G_sign lid sigma@(ExtSign s _) ind) =
    GMorphism (mkIdComorphism lid (top_sublogic lid))
              sigma ind (ide lid s) 0
  comp _
       (GMorphism r1 sigma1 ind1 mor1 _)
       (GMorphism r2 _sigma2 _ mor2 _) =
    do let lid1 = sourceLogic r1
           lid2 = targetLogic r1
           lid3 = sourceLogic r2
           lid4 = targetLogic r2
       mor1' <- coerceMorphism lid2 lid3 "Grothendieck.comp" mor1
       mor1'' <- map_morphism r2 mor1'
       mor <- comp lid4 mor1'' mor2
       if isIdComorphism (Comorphism r1) &&
          case coerceSublogic lid2 lid3 "Grothendieck.comp"
                              (targetSublogic r1) of
            Just sl1 -> maybe (error ("Logic.Grothendieck: Category "++
                                      "instance.comp: no mapping for " ++
                                      show sl1))
                              (isSubElem (targetSublogic r2))
                              (mapSublogic r2 sl1)
            _ -> False
         then do
           sigma1' <- coerceSign lid1 lid3 "Grothendieck.comp" sigma1
           return (GMorphism r2 sigma1' ind1 mor 0)
         else if isIdComorphism (Comorphism r2)
           then do mor2' <- coerceMorphism lid4 lid2 "Grothendieck.comp" mor2
                   mor' <- comp lid2 mor1 mor2'
                   return (GMorphism r1 sigma1 ind1 mor' 0)
           else return (GMorphism (CompComorphism r1 r2) sigma1 ind1 mor 0)
  dom _ (GMorphism r sigma ind _mor _) =
    G_sign (sourceLogic r) sigma ind
  cod _ (GMorphism r _sigma _ mor _) =
    G_sign lid2 (mkExtSign $ cod lid2 mor) 0
    where lid2 = targetLogic r
  legal_obj _ (G_sign lid (ExtSign sigma _) _) = legal_obj lid sigma
  legal_mor _ (GMorphism r (ExtSign s _) _ mor _) =
    legal_mor lid2 mor &&
    case maybeResult $ map_sign r s of
      Just (sigma',_) -> sigma' == cod lid2 mor
      Nothing -> False
    where lid2 = targetLogic r

-- | Embedding of homogeneous signature morphisms as Grothendieck sig mors
gEmbed2 :: G_sign -> G_morphism -> GMorphism
gEmbed2 (G_sign lid2 sig si) (G_morphism lid _ mor ind _) =
  let cid = mkIdComorphism lid (top_sublogic lid)
      Just sig1 = coerceSign lid2 (sourceLogic cid) "gEmbed2" sig
  in GMorphism cid sig1 si mor ind

-- | Embedding of homogeneous signature morphisms as Grothendieck sig mors
gEmbed :: G_morphism -> GMorphism
gEmbed (G_morphism lid s1 mor ind _) =
  GMorphism (mkIdComorphism lid (top_sublogic lid))
                (mkExtSign $ dom lid mor) s1 mor ind

-- | Embedding of comorphisms as Grothendieck sig mors
gEmbedComorphism :: AnyComorphism -> G_sign -> Result GMorphism
gEmbedComorphism (Comorphism cid) (G_sign lid sig ind) = do
  sig'@(ExtSign s _) <- coerceSign lid (sourceLogic cid) "gEmbedComorphism" sig
  (sigTar,_) <- map_sign cid s
  let lidTar = targetLogic cid
  return (GMorphism cid sig' ind (ide lidTar sigTar) 0)

-- | heterogeneous union of two Grothendieck signatures
gsigUnion :: LogicGraph -> G_sign -> G_sign -> Result G_sign
gsigUnion lg gsig1@(G_sign lid1 (ExtSign sigma1 _) _)
          gsig2@(G_sign lid2 (ExtSign sigma2 _) _) =
  if language_name lid1 == language_name lid2
     then homogeneousGsigUnion gsig1 gsig2
     else do
      (Comorphism cid1, Comorphism cid2) <-
            logicUnion lg (Logic lid1) (Logic lid2)
      let lidS1 = sourceLogic cid1
          lidS2 = sourceLogic cid2
          lidT1 = targetLogic cid1
          lidT2 = targetLogic cid2
      sigma1' <- coercePlainSign lid1 lidS1 "Union of signaturesa" sigma1
      sigma2' <- coercePlainSign lid2 lidS2 "Union of signaturesb" sigma2
      (sigma1'',_) <- map_sign cid1 sigma1'  -- where to put axioms???
      (sigma2'',_) <- map_sign cid2 sigma2'  -- where to put axioms???
      sigma2''' <- coercePlainSign lidT2 lidT1 "Union of signaturesc" sigma2''
      sigma3 <- signature_union lidT1 sigma1'' sigma2'''
      return (G_sign lidT1 (mkExtSign sigma3) 0)

-- | homogeneous Union of two Grothendieck signatures
homogeneousGsigUnion :: G_sign -> G_sign -> Result G_sign
homogeneousGsigUnion (G_sign lid1 sigma1 _) (G_sign lid2 sigma2 _) = do
  sigma2' <- coerceSign lid2 lid1 "Union of signaturesd" sigma2
  sigma3 <- ext_signature_union lid1 sigma1 sigma2'
  return (G_sign lid1 sigma3 0)

-- | union of a list of Grothendieck signatures
gsigManyUnion :: LogicGraph -> [G_sign] -> Result G_sign
gsigManyUnion _ [] =
  fail "union of emtpy list of signatures"
gsigManyUnion lg (gsigma : gsigmas) =
  foldM (gsigUnion lg) gsigma gsigmas

-- | homogeneous Union of a list of morphisms
homogeneousMorManyUnion :: [G_morphism] -> Result G_morphism
homogeneousMorManyUnion [] =
  fail "homogeneous union of emtpy list of morphisms"
homogeneousMorManyUnion (gmor : gmors) =
  foldM ( \ (G_morphism lid2 _ mor2 _ _) (G_morphism lid1 _ mor1 _ _) -> do
            mor1' <- coerceMorphism lid1 lid2  "homogeneousMorManyUnion" mor1
            mor <- morphism_union lid2 mor1' mor2
            return (G_morphism lid2 0 mor 0 0)) gmor gmors

-- | inclusion between two logics
logicInclusion :: LogicGraph -> AnyLogic -> AnyLogic -> Result AnyComorphism
logicInclusion logicGraph l1@(Logic lid1) (Logic lid2) =
     let ln1 = language_name lid1
         ln2 = language_name lid2 in
     if ln1==ln2 then
       return (idComorphism l1)
      else case Map.lookup (ln1,ln2) (inclusions logicGraph) of
           Just (Comorphism i) ->
               return (Comorphism i)
           Nothing ->
               fail ("No inclusion from "++ln1++" to "++ln2++" found")

updateMorIndex :: Int -> GMorphism -> GMorphism
updateMorIndex i (GMorphism cid sign si mor _) = GMorphism cid sign si mor i

toG_morphism :: GMorphism -> G_morphism
toG_morphism (GMorphism cid _ _ mor i) = G_morphism (targetLogic cid) 0 mor i 0

-- | inclusion morphism between two Grothendieck signatures
ginclusion :: LogicGraph -> G_sign -> G_sign -> Result GMorphism
ginclusion logicGraph (G_sign lid1 sigma1 ind) (G_sign lid2 sigma2 _) = do
    Comorphism i <- logicInclusion logicGraph (Logic lid1) (Logic lid2)
    ext1@(ExtSign sigma1' _) <-
        coerceSign lid1 (sourceLogic i) "Inclusion of signatures" sigma1
    (sigma1'',_) <- map_sign i sigma1'
    ExtSign sigma2' _ <-
        coerceSign lid2 (targetLogic i) "Inclusion of signatures" sigma2
    unless (is_subsig (targetLogic i) sigma1'' sigma2') $
        fail $ showDoc sigma1'' "\nis not a sub-signature of\n" ++
             showDoc sigma2' ""
    mor <- inclusion (targetLogic i) sigma1'' sigma2'
    return (GMorphism i ext1 ind mor 0)

-- | Composition of two Grothendieck signature morphisms
-- | with itermediate inclusion
compInclusion :: LogicGraph -> GMorphism -> GMorphism -> Result GMorphism
compInclusion lg mor1 mor2 = do
  let sigma1 = cod Grothendieck mor1
      sigma2 = dom Grothendieck mor2
  unless (isSubGsign lg sigma1 sigma2)
         (fail "Logic.Grothendieck.compInclusion: not a subsignature")
  incl <- ginclusion lg sigma1 sigma2
  mor <- comp Grothendieck mor1 incl
  comp Grothendieck mor mor2

-- | Composition of two Grothendieck signature morphisms
-- | with intermediate homogeneous inclusion
compHomInclusion :: GMorphism -> GMorphism -> Result GMorphism
compHomInclusion mor1 mor2 = compInclusion emptyLogicGraph mor1 mor2

-- | Find all (composites of) comorphisms starting from a given logic
findComorphismPaths :: LogicGraph ->  G_sublogics -> [AnyComorphism]
findComorphismPaths lg (G_sublogics lid sub) =
  nub $ map fst $ iterateComp (0::Int) [(idc,[idc])]
  where
  idc = Comorphism (mkIdComorphism lid sub)
  coMors = Map.elems $ comorphisms lg
  -- compute possible compositions, but only up to depth 3
  iterateComp n l = -- (l::[(AnyComorphism,[AnyComorphism])]) =
    if n>3 || l==newL then newL else iterateComp (n+1) newL
    where
    newL = nub (l ++ (concat (map extend l)))
    -- extend comorphism list in all directions, but no cylces
    extend (coMor, cmps) =
       let addCoMor c =
            case compComorphism coMor c of
              Nothing -> Nothing
              Just c1 -> Just (c1, c : cmps)
        in catMaybes $ map addCoMor $ filter (not . (`elem` cmps)) $ coMors

-- | finds first comorphism with a matching sublogic
findComorphism ::Monad m => G_sublogics -> [AnyComorphism] -> m AnyComorphism
findComorphism _ [] = fail "No matching comorphism found"
findComorphism gsl@(G_sublogics lid sub) ((Comorphism cid):rest) =
    let l2 = sourceLogic cid
        rec = findComorphism gsl rest in
   if language_name lid == language_name l2
      then if isSubElem (forceCoerceSublogic lid l2 sub) $ sourceSublogic cid
              then return $ Comorphism cid
              else rec
      else rec

-- | check transportability of Grothendieck signature morphisms
-- | (currently returns false for heterogeneous morphisms)
isTransportable :: GMorphism -> Bool
isTransportable (GMorphism cid _ ind1 mor ind2) = ind1 >0 && ind2 >0
    && isModelTransportable(Comorphism cid)
    && is_transportable (targetLogic cid) mor

-- * Provers

-- | provers and consistency checkers for specific logics
data G_prover = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
       G_prover lid (Prover sign sentence sublogics proof_tree)
  deriving Typeable

getProverName :: G_prover -> String
getProverName (G_prover _ p) = prover_name p

coerceProver ::
  (Logic  lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1,
   Logic  lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2,
   Monad m) => lid1 -> lid2 -> String
      -> Prover sign1 sentence1 sublogics1 proof_tree1
      -> m (Prover sign2 sentence2 sublogics2 proof_tree2)
coerceProver l1 l2 msg m1 = primCoerce l1 l2 msg m1

data G_cons_checker = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
       G_cons_checker lid
                (ConsChecker sign sentence sublogics morphism proof_tree)
  deriving Typeable

coerceConsChecker ::
  (Logic  lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1,
   Logic  lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2,
   Monad m) => lid1 -> lid2 -> String
      -> ConsChecker sign1 sentence1 sublogics1 morphism1 proof_tree1
      -> m (ConsChecker sign2 sentence2 sublogics2 morphism2 proof_tree2)
coerceConsChecker l1 l2 msg m1 = primCoerce l1 l2 msg m1

coerceG_sign ::
   (Logic  lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1,
   Monad m) => lid1 -> String -> G_sign -> m sign1
coerceG_sign l1 msg (G_sign l2 sign2 _) = primCoerce l2 l1 msg sign2
