{- |
Module      :  $Header$
Description :  parts of the tabular package
Copyright   :  (c) Eric Kow <E.Y.Kow@brighton.ac.uk>
License     :  BSD3

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

-}

module Common.Lib.Tabular where

import Data.List (intersperse, transpose)
import Common.Lib.State (evalState, get, put)

data Properties = NoLine | SingleLine | DoubleLine
data Header h = Header h | Group Properties [Header h]

{- |
> example = Table
>   (Group SingleLine
>      [ Group NoLine [Header "A 1", Header "A 2"]
>      , Group NoLine [Header "B 1", Header "B 2", Header "B 3"]
>      ])
>   (Group DoubleLine
>      [ Group SingleLine [Header "memtest 1", Header "memtest 2"]
>      , Group SingleLine [Header "time test 1", Header "time test 2"]
>      ])
>   [ ["hog", "terrible", "slow", "slower"]
>   , ["pig", "not bad",  "fast", "slowest"]
>   , ["good", "awful" ,  "intolerable", "bearable"]
>   , ["better", "no chance", "crawling", "amazing"]
>   , ["meh",  "well...", "worst ever", "ok"]
>   ]
> > putStr $ render id id id example
> +-----++-----------+-----------++-------------+-------------+
> |     || memtest 1 | memtest 2 || time test 1 | time test 2 |
> +=====++===========+===========++=============+=============+
> | A 1 ||       hog |  terrible ||        slow |      slower |
> | A 2 ||       pig |   not bad ||        fast |     slowest |
> +-----++-----------+-----------++-------------+-------------+
> | B 1 ||      good |     awful || intolerable |    bearable |
> | B 2 ||    better | no chance ||    crawling |     amazing |
> | B 3 ||       meh |   well... ||  worst ever |          ok |
> +-----++-----------+-----------++-------------+-------------+
-}
data Table rh ch a = Table (Header rh) (Header ch) [[a]]

-- * Helper functions for rendering

-- | Retrieve the contents of a  header
headerContents :: Header h -> [h]
headerContents (Header s) = [s]
headerContents (Group _ hs) = concatMap headerContents hs

instance Functor Header where
 fmap f (Header s) = Header (f s)
 fmap f (Group p hs) = Group p (map (fmap f) hs)

{- | 'zipHeader' @e@ @ss@ @h@ returns the same structure
  as @h@ except with all the text replaced by the contents
  of @ss@.

  If @ss@ has too many cells, the excess is ignored.
  If it has too few cells, the missing ones (at the end)
  and replaced with the empty contents @e@.
-}
zipHeader :: h -> [h] -> Header a -> Header (h, a)
zipHeader e ss h = evalState (helper h) ss
 where
  helper (Header x) =
   do cells <- get
      string <- case cells of
                  [] -> return (e, x)
                  s : xs -> put xs >> return (s, x)
      return $ Header string
  helper (Group s hs) =
   Group s `fmap` mapM helper hs

flattenHeader :: Header h -> [Either Properties h]
flattenHeader (Header s) = [Right s]
flattenHeader (Group l s) =
  concat . intersperse [Left l] . map flattenHeader $ s

{- | The idea is to deal with the fact that Properties
  (e.g. borders) are not standalone cells but attributes
  of a cell.  A border is just a CSS decoration of a
  TD element.

  squish @decorator f h@ applies @f@ to every item
  in the list represented by @h@ (see 'flattenHeader'),
  additionally applying @decorator@ if the item is
  followed by some kind of boundary

  So
    @
    o o o | o o o | o o
    @
  gets converted into
    @
    O O X   O O X   O O
    @
-}
squish :: (Properties -> b -> b)
       -> (h -> b)
       -> Header h
       -> [b]
squish decorator f h = helper $ flattenHeader h
 where
  helper [] = []
  helper (Left _ : es) = helper es
  helper (Right x : es) =
   case es of
     (Left p : es2) -> decorator p (f x) : helper es2
     _ -> f x : helper es

-- * Combinators

{- | Convenience type for just one row (or column).
  To be used with combinators as follows:

> example2 =
>   empty ^..^ col "memtest 1" [] ^|^ col "memtest 2"   []
>         ^||^ col "time test "[] ^|^ col "time test 2" []
>   +.+ row "A 1" ["hog", "terrible", "slow", "slower"]
>   +.+ row "A 2" ["pig", "not bad", "fast", "slowest"]
>   +----+
>       row "B 1" ["good", "awful", "intolerable", "bearable"]
>   +.+ row "B 2" ["better", "no chance", "crawling", "amazing"]
>   +.+ row "B 3" ["meh",  "well...", "worst ever", "ok"]
-}
data SemiTable h a = SemiTable (Header h) [a]

empty :: Table rh ch a
empty = Table (Group NoLine []) (Group NoLine []) []

col :: ch -> [a] -> SemiTable ch a
col = SemiTable . Header

-- | Column header
colH :: ch -> SemiTable ch a
colH header = col header []

row :: rh -> [a] -> SemiTable rh a
row = col

rowH :: rh -> SemiTable rh a
rowH = colH

beside :: Properties -> Table rh ch a -> SemiTable ch a -> Table rh ch a
beside prop (Table rows cols1 data1)
            (SemiTable cols2 data2) =
  Table rows (Group prop [cols1, cols2])
             (zipWith (++) data1 [data2])

below :: Properties -> Table rh ch a -> SemiTable rh a -> Table rh ch a
below prop (Table rows1 cols data1)
           (SemiTable rows2 data2) =
  Table (Group prop [rows1, rows2]) cols (data1 ++ [data2])

-- | besides
(^..^) :: Table rh ch a -> SemiTable ch a -> Table rh ch a
(^..^) = beside NoLine

-- | besides with a line
(^|^) :: Table rh ch a -> SemiTable ch a -> Table rh ch a
(^|^) = beside SingleLine

-- | besides with a double line
(^||^) :: Table rh ch a -> SemiTable ch a -> Table rh ch a
(^||^) = beside DoubleLine

-- | below
(+.+) :: Table rh ch a -> SemiTable rh a -> Table rh ch a
(+.+) = below NoLine

-- | below with a line
(+----+) :: Table rh ch a -> SemiTable rh a -> Table rh ch a
(+----+) = below SingleLine

-- | below with a double line
(+====+) :: Table rh ch a -> SemiTable rh a -> Table rh ch a
(+====+) = below DoubleLine

-- * ascii art

-- | for simplicity, we assume that each cell is rendered on a single line
render :: (rh -> String)
       -> (ch -> String)
       -> (a -> String)
       -> Table rh ch a
       -> String
render fr fc f (Table rh ch cells) =
  unlines $ [ bar SingleLine   -- +--------------------------------------+
            , renderColumns sizes ch2
            , bar DoubleLine   -- +======================================+
            ] ++
            renderRs (fmap renderR $ zipHeader [] cells $ fmap fr rh) ++
            [ bar SingleLine ] -- +--------------------------------------+
 where
  bar = concat . renderHLine sizes ch2
  -- ch2 and cell2 include the row and column labels
  ch2 = Group DoubleLine [Header "", fmap fc ch]
  cells2 = headerContents ch2
         : zipWith (\ h cs -> h : map f cs) rhStrings cells
  renderR (cs, h) = renderColumns sizes $ Group DoubleLine
                    [ Header h
                    , fmap fst $ zipHeader "" (map f cs) ch]
  rhStrings = map fr $ headerContents rh
  -- maximum width for each column
  sizes = map (maximum . map length) . transpose $ cells2
  renderRs (Header s) = [s]
  renderRs (Group p hs) = concat . intersperse sep . map renderRs $ hs
    where sep = renderHLine sizes ch2 p

-- | We stop rendering on the shortest list!
renderColumns :: [Int] -- ^ max width for each column
              -> Header String
              -> String
renderColumns is h = "| " ++ coreLine ++ " |"
 where
  coreLine = concatMap helper $ flattenHeader $ zipHeader 0 is h
  padLeft (l, s) = replicate (l - length s) ' ' ++ s
  helper = either hsep padLeft
  hsep :: Properties -> String
  hsep NoLine = " "
  hsep SingleLine = " | "
  hsep DoubleLine = " || "

renderHLine :: [Int] -- ^ width specifications
            -> Header String
            -> Properties
            -> [String]
renderHLine _ _ NoLine = []
renderHLine w h SingleLine = [renderHLine' w '-' h]
renderHLine w h DoubleLine = [renderHLine' w '=' h]

renderHLine' :: [Int] -> Char -> Header String -> String
renderHLine' is sep h = [ '+', sep ] ++ coreLine ++ [sep, '+']
 where
  coreLine = concatMap helper $ flattenHeader $ zipHeader 0 is h
  helper = either vsep dashes
  dashes (i, _) = replicate i sep
  vsep NoLine = [sep]
  vsep SingleLine = sep : '+' : [sep]
  vsep DoubleLine = sep : "++" ++ [sep]
