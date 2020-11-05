{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}
{- |
Module      :  ./Common/AS_Annotation.der.hs
Description :  datastructures for annotations of (Het)CASL.
Copyright   :  (c) Klaus Luettich, Christian Maeder, and Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Datastructures for annotations of (Het)CASL.
   There is also a paramterized data type for an 'Annoted' 'item'.
   See also chapter II.5 of the CASL Reference Manual.
-}

module Common.AS_Annotation where
import Common.Id
import Common.IRI (IRI)

import Data.Data
import Data.Maybe
import qualified Data.HashMap.Lazy as Map

import Data.Hashable
import GHC.Generics (Generic)

import Data.Graph.Inductive.Graph as Graph

-- DrIFT command
{-! global: GetRange !-}

-- | start of an annote with its WORD or a comment
data Annote_word = Annote_word String | Comment_start
  deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable Annote_word

-- | line or group for 'Unparsed_anno'
data Annote_text = Line_anno String | Group_anno [String]
    deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable Annote_text

{- | formats to be displayed (may be extended in the future).
Drop 3 from the show result to get the string for parsing and printing -}
data Display_format = DF_HTML | DF_LATEX | DF_RTF
  deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable Display_format

-- | swap the entries of a lookup table
swapTable :: [(a, b)] -> [(b, a)]
swapTable = map $ \ (a, b) -> (b, a)

-- | drop the first 3 characters from the show result
toTable :: (Show a) => [a] -> [(a, String)]
toTable = map $ \ a -> (a, drop 3 $ show a)

-- | a lookup table for the textual representation of display formats
display_format_table :: [(Display_format, String)]
display_format_table = toTable [ DF_HTML, DF_LATEX, DF_RTF ]

{- | lookup the textual representation of a display format
in 'display_format_table' -}
lookupDisplayFormat :: Display_format -> String
lookupDisplayFormat df =
    fromMaybe (error "lookupDisplayFormat: unknown display format")
        $ lookup df display_format_table

{- | precedence 'Lower' means less and 'BothDirections' means less and greater.
'Higher' means greater but this is syntactically not allowed in 'Prec_anno'.
'NoDirection' can also not be specified explicitly,
but covers those ids that are not mentionend in precedences. -}
data PrecRel = Higher | Lower | BothDirections | NoDirection
    deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable PrecRel

-- | either left or right associative
data AssocEither = ALeft | ARight deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable AssocEither

{- | semantic (line) annotations without further information.
Use the same drop-3-trick as for the 'Display_format'. -}
data Semantic_anno = SA_cons | SA_def | SA_implies | SA_mono | SA_implied
                   | SA_mcons | SA_ccons | SA_wdef
    deriving (Show, Eq, Ord, Typeable, Data, Enum, Bounded, Generic)

instance Hashable Semantic_anno

-- | a lookup table for the textual representation of semantic annos
semantic_anno_table :: [(Semantic_anno, String)]
semantic_anno_table =
  toTable [minBound .. maxBound]

{- | lookup the textual representation of a semantic anno
in 'semantic_anno_table' -}
lookupSemanticAnno :: Semantic_anno -> String
lookupSemanticAnno sa =
    fromMaybe (error "lookupSemanticAnno: no semantic anno")
        $ lookup sa semantic_anno_table

-- | all possible annotations (without comment-outs)
data Annotation = -- | constructor for comments or unparsed annotes
                Unparsed_anno Annote_word Annote_text Range
                -- | known annotes
                | Display_anno Id [(Display_format, String)] Range
                -- position of anno start, keywords and anno end
                | List_anno Id Id Id Range
                -- position of anno start, commas and anno end
                | Number_anno Id Range
                -- position of anno start, commas and anno end
                | Float_anno Id Id Range
                -- position of anno start, commas and anno end
                | String_anno Id Id Range
                -- position of anno start, commas and anno end
                | Prec_anno PrecRel [Id] [Id] Range
                {- positions: "{",commas,"}", RecRel, "{",commas,"}"
                Lower = "< "  BothDirections = "<>" -}
                | Assoc_anno AssocEither [Id] Range -- position of commas
                | Label [String] Range
                -- position of anno start and anno end
                | Prefix_anno [(String, IRI)] Range
                -- position of anno start and anno end

                -- All annotations below are only as annote line allowed
                | Semantic_anno Semantic_anno Range
                {- position information for annotations is provided
                by every annotation -}
                  deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable Annotation

{- | 'isLabel' tests if the given 'Annotation' is a label
(a 'Label' typically follows a formula) -}
isLabel :: Annotation -> Bool
isLabel a = case a of
    Label _ _ -> True
    _ -> False

isImplies :: Annotation -> Bool
isImplies a = case a of
    Semantic_anno SA_implies _ -> True
    _ -> False

isImplied :: Annotation -> Bool
isImplied a = case a of
    Semantic_anno SA_implied _ -> True
    _ -> False

-- | 'isSemanticAnno' tests if the given 'Annotation' is a semantic one
isSemanticAnno :: Annotation -> Bool
isSemanticAnno a = case a of
    Semantic_anno _ _ -> True
    _ -> False

{- | 'isComment' tests if the given 'Annotation' is a comment line or a
comment group -}
isComment :: Annotation -> Bool
isComment c = case c of
    Unparsed_anno Comment_start _ _ -> True
    _ -> False

-- | 'isAnnote' is the negation of 'isComment'
isAnnote :: Annotation -> Bool
isAnnote = not . isComment

-- | separate prefix annotations and put them into a map
partPrefixes :: [Annotation] -> (Map.HashMap String IRI, [Annotation])
partPrefixes = foldr (\ a (m, l) -> case a of
    Prefix_anno p _ -> (Map.union m $ Map.fromList p, l)
    _ -> (m, a : l)) (Map.empty, [])

{- | an item wrapped in preceding (left 'l_annos')
and following (right 'r_annos') annotations.
'opt_pos' should carry the position of an optional semicolon
following a formula (but is currently unused). -}
data Annoted a = Annoted
    { item :: a
    , opt_pos :: Range
    , l_annos :: [Annotation]
    , r_annos :: [Annotation] } deriving (Show, Ord, Eq, Typeable, Data, Generic)

instance Hashable a => Hashable (Annoted a)

annoRange :: (a -> [Pos]) -> Annoted a -> [Pos]
annoRange f a =
  joinRanges $ map (rangeToList . getRange) (l_annos a) ++ [f $ item a]
  ++ [rangeToList (opt_pos a)] ++ map (rangeToList . getRange) (r_annos a)

notImplied :: Annoted a -> Bool
notImplied = not . any isImplied . r_annos

-- | origin of sentences

data SenOrigin = SenOrigin 
     { dGraphName :: IRI
     , originNodeId :: Node
     , senName :: String } deriving (Eq, Ord, Show, Typeable, Data)

-- | naming or labelling sentences
data SenAttr s a = SenAttr
    { senAttr :: a
    , priority :: Maybe String
    , isAxiom :: Bool
    , isDef :: Bool
    , wasTheorem :: Bool
      {- will be set to True when status of isAxiom
         changes from False to True -}
    , simpAnno :: Maybe Bool -- for %simp or %nosimp annotations
    , attrOrigin :: Maybe Id
    , senMark :: String -- a marker for theoroidal comorphisms
    , senOrigin :: Maybe SenOrigin 
       -- Nothing for local sentences, Just (libName as iri, node, sentence name) for imported ones
    , sentence :: s } deriving (Eq, Ord, Show, Typeable, Data)

-- | equip a sentence with a name
makeNamed :: a -> s -> SenAttr s a
makeNamed a s = SenAttr
  { senAttr = a
  , priority = Nothing
  , isAxiom = True
  , isDef = False
  , wasTheorem = False
  , simpAnno = Nothing
  , attrOrigin = Nothing
  , senMark = ""
  , senOrigin = Nothing
  , sentence = s }

-- | set the origin of a named sentence
setOrigin :: IRI -> Node -> String -> SenAttr s a -> SenAttr s a
setOrigin lib node sen nsen = nsen {senOrigin = Just $ SenOrigin lib node sen} 

-- | set the origin of a named sentence, if the sentence does not already have an origin, owise leave unchanged
setOriginIfLocal :: IRI -> Node -> String -> SenAttr s a -> SenAttr s a
setOriginIfLocal lib node sen nsen = 
 case senOrigin nsen of
  Nothing -> setOrigin lib node sen nsen
  _ -> nsen

type Named s = SenAttr s String

markSen :: String -> Named s -> Named s
markSen m n = n { senMark = m }

unmark :: Named s -> Named s
unmark = markSen ""

reName :: (a -> b) -> SenAttr s a -> SenAttr s b
reName f x = x { senAttr = f $ senAttr x }

-- | extending sentence maps to maps on labelled sentences
mapNamed :: (s -> t) -> SenAttr s a -> SenAttr t a
mapNamed f x = x { sentence = f $ sentence x }

-- | extending sentence maybe-maps to maps on labelled sentences
mapNamedM :: Monad m => (s -> m t) -> Named s -> m (Named t)
mapNamedM f x = do
  y <- f $ sentence x
  return x {sentence = y}

-- | process all items and wrap matching annotations around the results
mapAnM :: (Monad m) => (a -> m b) -> [Annoted a] -> m [Annoted b]
mapAnM f al =
    do il <- mapM (f . item) al
       return $ zipWith (flip replaceAnnoted) al il

instance Functor Annoted where
    fmap f (Annoted x o l r) = Annoted (f x) o l r

-- | replace the 'item'
replaceAnnoted :: b -> Annoted a -> Annoted b
replaceAnnoted x (Annoted _ o l r) = Annoted x o l r
{- one could use this fmap variant instead (less efficient)
replaceAnnoted x = fmap (const x)
or even:
replaceAnnoted = (<$) -}

-- | add further following annotations
appendAnno :: Annoted a -> [Annotation] -> Annoted a
appendAnno (Annoted x p l r) = Annoted x p l . (r ++)

-- | put together preceding annotations and an item
addLeftAnno :: [Annotation] -> a -> Annoted a
addLeftAnno l i = Annoted i nullRange l []

-- | decorate with no annotations
emptyAnno :: a -> Annoted a
emptyAnno = addLeftAnno []

-- | get the label following (or to the right of) an 'item'
getRLabel :: Annoted a -> String
getRLabel a =
    case filter isLabel (r_annos a) of
      Label l _ : _ -> unwords $ concatMap words l
      _ -> ""

{- | check for an annotation starting with % and the input str
(does not work for known annotation words) -}
identAnno :: String -> Annotation -> Bool
identAnno str an = case an of
    Unparsed_anno (Annote_word wrd) _ _ -> wrd == str
    _ -> False

-- | test all anntotions for an item
hasIdentAnno :: String -> Annoted a -> Bool
hasIdentAnno str a = any (identAnno str) $ l_annos a ++ r_annos a

getPriority :: [Annotation] -> Maybe String
getPriority = foldl
  (\ mId anno -> case anno of
    Unparsed_anno (Annote_word "priority") (Group_anno (x : _)) _ -> Just x
    _ -> mId
  ) Nothing

makeNamedSen :: Annoted a -> Named a
makeNamedSen a = (makeNamed (getRLabel a) $ item a)
  { isAxiom = notImplied a
  , priority = getPriority $ r_annos a
  , simpAnno = case (hasIdentAnno "simp" a, hasIdentAnno "nosimp" a) of
    (True, False) -> Just True
    (False, True) -> Just False
    _ -> Nothing }

annoArg :: Annote_text -> String
annoArg txt = case txt of
  Line_anno str -> str
  Group_anno ls -> unlines ls

newtype Name = Name String deriving Typeable

instance Show Name where
  show (Name s) = s

getAnnoName :: Annoted a -> Name
getAnnoName = Name . foldr (\ an -> case an of
  Unparsed_anno (Annote_word wrd) txt _ | wrd == "name" ->
     (annoArg txt ++)
  _ -> id) "" . l_annos
