-- | Note: the core types and comibnators
--   from this module are from Toxaris in a #haskell
--   conversation on 2008-08-24
module Text.Tabular where

import Data.List (intersperse)
import Control.Monad.State (evalState, State, get, put)

data Properties = NoLine | SingleLine | DoubleLine
data Header h = Header h | Group Properties [Header h]

-- |
-- > example = Table
-- >   (Group SingleLine
-- >      [ Group NoLine [Header "A 1", Header "A 2"]
-- >      , Group NoLine [Header "B 1", Header "B 2", Header "B 3"]
-- >      ])
-- >   (Group DoubleLine
-- >      [ Group SingleLine [Header "memtest 1", Header "memtest 2"]
-- >      , Group SingleLine [Header "time test 1", Header "time test 2"]
-- >      ])
-- >   [ ["hog", "terrible", "slow", "slower"]
-- >   , ["pig", "not bad",  "fast", "slowest"]
-- >   , ["good", "awful" ,  "intolerable", "bearable"]
-- >   , ["better", "no chance", "crawling", "amazing"]
-- >   , ["meh",  "well...", "worst ever", "ok"]
-- >   ]
--
-- > -- Text.Tabular.AsciiArt.render example id
-- > --
-- > --     || memtest 1 | memtest 2 ||  time test  | time test 2
-- > -- ====++===========+===========++=============+============
-- > -- A 1 ||       hog |  terrible ||        slow |      slower
-- > -- A 2 ||       pig |   not bad ||        fast |     slowest
-- > -- ----++-----------+-----------++-------------+------------
-- > -- B 1 ||      good |     awful || intolerable |    bearable
-- > -- B 2 ||    better | no chance ||    crawling |     amazing
-- > -- B 3 ||       meh |   well... ||  worst ever |          ok
data Table a = Table (Header String) (Header String) [[a]]

-- ----------------------------------------------------------------------
-- * Helper functions for rendering
-- ----------------------------------------------------------------------

-- | Retrieve the strings in a header
headerStrings :: Header String -> [String]
headerStrings (Header s) = [s]
headerStrings (Group _ hs) = concatMap headerStrings hs

instance Functor Header where
 fmap f (Header s)   = Header (f s)
 fmap f (Group p hs) = Group p (map (fmap f) hs)

-- | 'zipHeader' @e@ @ss@ @h@ returns the same structure
--   as @h@ except with all the text replaced by the contents
--   of @ss@.
--
--   If @ss@ has too many cells, the excess is ignored.
--   If it has too few cells, the missing ones (at the end)
--   and replaced with the empty contents @e@
zipHeader :: h -> [h] -> Header a -> Header (h,a)
zipHeader e ss h = evalState (helper h) ss
 where
  helper (Header x) =
   do cells  <- get
      string <- case cells of
                  []     -> return (e,x)
                  (s:ss) -> put ss >> return (s,x)
      return $ Header string
  helper (Group s hs) =
   Group s `fmap` mapM helper hs

flattenHeader :: Header h -> [Either Properties h]
flattenHeader (Header s) = [Right s]
flattenHeader (Group l s) =
  concat . intersperse [Left l] . map flattenHeader $ s

-- | The idea is to deal with the fact that Properties
--   (e.g. borders) are not standalone cells but attributes
--   of a cell.  A border is just a CSS decoration of a
--   TD element.
--
--   squish @decorator f h@ applies @f@ to every item
--   in the list represented by @h@ (see 'flattenHeader'),
--   additionally applying @decorator@ if the item is
--   followed by some kind of boundary
--
--   So
--   @
--     o o o | o o o | o o
--   @
--   gets converted into
--   @
--     O O X   O O X   O O
--   @
squish :: (Properties -> b -> b)
       -> (h -> b)
       -> Header h
       -> [b]
squish decorator f h = helper $ flattenHeader h
 where
  helper [] = []
  helper (Left p:es)  = helper es
  helper (Right x:es) =
   case es of
     (Left p:es2) -> decorator p (f x) : helper es2
     _            -> f x : helper es

-- ----------------------------------------------------------------------
-- * Combinators
-- ----------------------------------------------------------------------

-- | Convenience type for just one row (or column).
--   To be used with combinators as follows:
--
-- > example2 =
-- >   empty ^..^ col "memtest 1" [] ^|^ col "memtest 2"   []
-- >         ^||^ col "time test "[] ^|^ col "time test 2" []
-- >   +.+ row "A 1" ["hog", "terrible", "slow", "slower"]
-- >   +.+ row "A 2" ["pig", "not bad", "fast", "slowest"]
-- >   +----+
-- >       row "B 1" ["good", "awful", "intolerable", "bearable"]
-- >   +.+ row "B 2" ["better", "no chance", "crawling", "amazing"]
-- >   +.+ row "B 3" ["meh",  "well...", "worst ever", "ok"]
data SemiTable a = SemiTable (Header String) [a]

empty :: Table a
empty = Table (Group NoLine []) (Group NoLine []) []

col :: String -> [a] -> SemiTable a
col header cells = SemiTable (Header header) cells

-- | Column header
colH :: String -> SemiTable a
colH header = col header []

row :: String -> [a] -> SemiTable a
row = col

rowH :: String -> SemiTable a
rowH = colH

beside :: Properties -> Table a -> SemiTable a -> Table a
beside prop (Table rows cols1 data1)
            (SemiTable  cols2 data2) =
  Table rows (Group prop [cols1, cols2])
             (zipWith (++) data1 [data2])

below :: Properties -> Table a -> SemiTable a -> Table a
below prop (Table     rows1 cols data1)
           (SemiTable rows2      data2) =
  Table (Group prop [rows1, rows2]) cols (data1 ++ [data2])

-- | besides
(^..^) = beside NoLine
-- | besides with a line
(^|^)  = beside SingleLine
-- | besides with a double line
(^||^) = beside DoubleLine

-- | below
(+.+) = below NoLine
-- | below with a line
(+----+) = below SingleLine
-- | below with a double line
(+====+) = below DoubleLine


