{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, and Uni Bremen 2002-2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  non-portable (various -fglasgow-exts extensions)


-- languages, define like "data CASL = CASL deriving Show" 
-}

module Logic.Languages where

-- for coercion used in Grothendieck.hs and Analysis modules

import UnsafeCoerce
import Data.Dynamic

import Common.Id
import Common.Result
import Data.Maybe


class Show lid => Language lid where
    language_name :: lid -> String
    language_name i = show i
    description :: lid -> String
    -- default implementation
    description _ = "No description available"

-- (a bit unsafe) coercion using the language name
mcoerce :: (Typeable a, Typeable b, Language lid1, Language lid2,
          Monad m) => lid1 -> lid2 -> String -> a -> m b
mcoerce i1 i2 err a = 
  if language_name i1 == language_name i2 
     then return $ unsafeCoerce a 
     else fail (err1++"Logic "++ language_name i1 ++ " expected, but "
                ++ language_name i2 ++ " found")
  where err1 = if err=="" then "" else err++": "
   
coerce :: (Typeable a, Typeable b, Language lid1, Language lid2,
          Monad m) => lid1 -> lid2 -> a -> m b
coerce i1 i2 a = mcoerce i1 i2 "" a 

idcoerce :: (Typeable a, Typeable b, Language lid1, Language lid2)
               => lid1 -> lid2 -> a -> b
idcoerce i1 i2 a = fromJust $ coerce i1 i2 a 

rcoerce :: (Typeable a, Typeable b, Language lid1, Language lid2) => 
           lid1 -> lid2 -> Pos -> a -> Result b
rcoerce i1 i2 pos a = adjustPos pos $ coerce i1 i2 a

mrcoerce :: (Typeable a, Typeable b, Language lid1, Language lid2) => 
           lid1 -> lid2 -> Pos -> String -> a -> Result b
mrcoerce i1 i2 pos err a = adjustPos pos $ mcoerce i1 i2 err a
