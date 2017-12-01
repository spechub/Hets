{- |
Module      :  ./TopHybrid/Utilities.hs
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  nevrenato@gmail.com
Stability   :  stable
Portability :  portable

Description : List of utilities for Hybridized logic
-}

module TopHybrid.Utilities where
import qualified Data.Map as M
import Data.Maybe
import Control.Monad
import Common.AS_Annotation
import Common.Result
import Common.Id

-- | Builds a map from a list of tuples
buildMapFromList :: (Ord a) => [(a, b)] -> M.Map a b
buildMapFromList = foldl (\ y (x, x') -> M.insert x x' y) M.empty

-- | List of message errors
msgsList :: [(Int, String)]
msgsList = [(0, msg0), (1, msg1), (2, msg2), (3, msg3), (4, msg4)]
        where
        msg0 = "Repeated nominals and/or modalities"
        msg1 = "Nominal not found"
        msg2 = "No static analyser for this logic"
        msg3 = "The chosen logic doesn't exist, or " ++
               "isn't available for hybridization"
        msg4 = "The chosen logic doesn't have a static analyser for formulas"

-- | Message errors as map
msgs :: M.Map Int String
msgs = buildMapFromList msgsList

-- | The generic error message
gErr :: String
gErr = "Unspecific error found"

-- | Lifter of the mkNamed function
liftName :: (Monad m) => String -> m a -> m (Named a)
liftName s = liftM $ makeNamed s

{- | Checks if a given computation was sucessfull, if not
gives an error message
Must i need this ? -}
maybeE :: Int -> Maybe a -> a
maybeE i = fromMaybe $ error $ fromMaybe gErr msg
        where msg = M.lookup i msgs

-- Gives an hint message
mkHint :: a -> String -> Result a
mkHint a s = hint a s nullRange
