{- |
Module      :  $Header$
Description :  datastructures for annotations of (Het)CASL.
Copyright   :  (c) Klaus Luettich, Christian Maeder, and Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Datastructures for annotations of (Het)CASL.
   There is also a paramterized data type for an 'Annoted' 'item'.
   See also chapter II.5 of the CASL Reference Manual.
-}

module Common.AS_Annotation where
import Common.Id
import Data.Maybe

-- DrIFT command
{-! global: GetRange !-}

-- | start of an annote with its WORD or a comment
data Annote_word = Annote_word String | Comment_start deriving (Show, Eq, Ord)

-- | line or group for 'Unparsed_anno'
data Annote_text = Line_anno String | Group_anno [String]
    deriving (Show, Eq, Ord)

-- | formats to be displayed (may be extended in the future).
-- Drop 3 from the show result to get the string for parsing and printing
data Display_format = DF_HTML | DF_LATEX | DF_RTF deriving (Show, Eq, Ord)

-- | swap the entries of a lookup table
swapTable :: [(a, b)] -> [(b, a)]
swapTable = map $ \ (a, b) -> (b, a)

-- | drop the first 3 characters from the show result
toTable :: (Show a) => [a] -> [(a, String)]
toTable = map $ \a -> (a, drop 3 $ show a)

-- | a lookup table for the textual representation of display formats
display_format_table :: [(Display_format, String)]
display_format_table = toTable [ DF_HTML, DF_LATEX, DF_RTF ]

-- | lookup the textual representation of a display format
-- in 'display_format_table'
lookupDisplayFormat :: Display_format -> String
lookupDisplayFormat df =
    fromMaybe (error "lookupDisplayFormat: unknown display format")
        $ lookup df display_format_table

-- | precedence 'Lower' means less and 'BothDirections' means less and greater.
-- 'Higher' means greater but this is syntactically not allowed in 'Prec_anno'.
-- 'NoDirection' can also not be specified explicitly,
-- but covers those ids that are not mentionend in precedences.
data PrecRel = Higher | Lower | BothDirections | NoDirection
    deriving (Show, Eq, Ord)

-- | either left or right associative
data AssocEither = ALeft | ARight deriving (Show, Eq, Ord)

-- | semantic (line) annotations without further information.
-- Use the same drop-3-trick as for the 'Display_format'.
data Semantic_anno = SA_cons | SA_def | SA_implies | SA_mono | SA_implied
    deriving (Show, Eq, Ord)

-- | a lookup table for the textual representation of semantic annos
semantic_anno_table :: [(Semantic_anno, String)]
semantic_anno_table =
    toTable [SA_cons, SA_def, SA_implies, SA_mono, SA_implied]

-- | lookup the textual representation of a semantic anno
-- in 'semantic_anno_table'
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
                --          ^ positions: "{",commas,"}", RecRel, "{",commas,"}"
                --          | Lower = "< "  BothDirections = "<>"
                | Assoc_anno AssocEither [Id] Range -- position of commas
                | Label [String] Range
                -- position of anno start and anno end

                -- All annotations below are only as annote line allowed
                | Semantic_anno Semantic_anno Range
                -- position information for annotations is provided
                -- by every annotation
                  deriving (Show, Eq, Ord)

-- |
-- 'isLabel' tests if the given 'Annotation' is a label
-- (a 'Label' typically follows a formula)
isLabel :: Annotation -> Bool
isLabel a = case a of
    Label _ _ -> True
    _         -> False

isImplies :: Annotation -> Bool
isImplies a = case a of
    Semantic_anno SA_implies _  -> True
    _ -> False

isImplied :: Annotation -> Bool
isImplied a = case a of
    Semantic_anno SA_implied _  -> True
    _ -> False

-- |
-- 'isSemanticAnno' tests if the given 'Annotation' is a semantic one
isSemanticAnno :: Annotation -> Bool
isSemanticAnno a = case a of
    Semantic_anno _ _  -> True
    _ -> False

-- |
-- 'isComment' tests if the given 'Annotation' is a comment line or a
-- comment group
isComment :: Annotation -> Bool
isComment c = case c of
    Unparsed_anno Comment_start _ _ -> True
    _ -> False

-- |
-- 'isAnnote' is the negation of 'isComment'
isAnnote :: Annotation -> Bool
isAnnote = not . isComment

-- | an item wrapped in preceeding (left 'l_annos')
-- and following (right 'r_annos') annotations.
-- 'opt_pos' should carry the position of an optional semicolon
-- following a formula (but is currently unused).
data Annoted a = Annoted
    { item :: a
    , opt_pos :: Range
    , l_annos :: [Annotation]
    , r_annos :: [Annotation] } deriving (Show, Ord, Eq)

annoRange :: (a -> [Pos]) -> Annoted a -> [Pos]
annoRange f a =
  joinRanges $ map (rangeToList . getRange) (l_annos a) ++ [f $ item a]
  ++ [rangeToList (opt_pos a)] ++ map (rangeToList . getRange) (r_annos a)

notImplied :: Annoted a -> Bool
notImplied = not . any isImplied . r_annos

-- | naming or labelling sentences
data SenAttr s a = SenAttr
    { senAttr  :: a
    , isAxiom :: Bool
    , isDef :: Bool
    , wasTheorem :: Bool
{- will be set to True when status of isAxiom changes from False to True -}
    , simpAnno :: Maybe Bool -- for %simp or %nosimp annotations
    , sentence :: s } deriving (Eq, Ord, Show)

-- | equip a sentence with a name
makeNamed :: a -> s -> SenAttr s a
makeNamed a s = SenAttr
  { senAttr = a
  , isAxiom = True
  , isDef = False
  , wasTheorem = False
  , simpAnno = Nothing
  , sentence = s }

type Named s = SenAttr s String

reName :: (String -> String) -> Named s -> Named s
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
-- one could use this fmap variant instead (less efficient)
-- replaceAnnoted x = fmap (const x)
-- or even:
-- replaceAnnoted = (<$)

-- | add further following annotations
appendAnno :: Annoted a -> [Annotation] -> Annoted a
appendAnno (Annoted x p l r) y = Annoted x p l $ r ++ y

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

-- | check for an annotation starting with % and the input str
--   (does not work for known annotation words)
identAnno :: String -> Annotation -> Bool
identAnno str an = case an of
    Unparsed_anno (Annote_word wrd) _ _ -> wrd == str
    _ -> False

-- | test all anntotions for an item
hasIdentAnno :: String -> Annoted a -> Bool
hasIdentAnno str a = any (identAnno str) $ l_annos a ++ r_annos a

makeNamedSen :: Annoted a -> Named a
makeNamedSen a = (makeNamed (getRLabel a) $ item a)
  { isAxiom = notImplied a
  , simpAnno = case (hasIdentAnno "simp" a, hasIdentAnno "nosimp" a) of
    (True, False) -> Just True
    (False, True) -> Just False
    _ -> Nothing }
