{- |
Module      :  $Header$
Copyright   :  (c) The University of Glasgow 2002
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  non-portable (GHC specific, 4 byte ints)

Unboxed mutable Ints

-}

module Common.Lib.FastMutInt(
	FastMutInt, newFastMutInt,
	readFastMutInt, writeFastMutInt,
	incFastMutInt, incFastMutIntBy
  ) where

import GHC.Base
import GHC.IOBase

data FastMutInt = FastMutInt (MutableByteArray# RealWorld)

newFastMutInt :: IO FastMutInt
newFastMutInt = IO $ \s0 ->
  case newByteArray# size s0 of { (# s, arr #) ->
  (# s, FastMutInt arr #) }
  where I# size = 4

readFastMutInt :: FastMutInt -> IO Int
readFastMutInt (FastMutInt arr) = IO $ \s0 ->
  case readIntArray# arr 0# s0 of { (# s, i #) ->
  (# s, I# i #) }

writeFastMutInt :: FastMutInt -> Int -> IO ()
writeFastMutInt (FastMutInt arr) (I# i) = IO $ \s0 ->
  case writeIntArray# arr 0# i s0 of { s ->
  (# s, () #) }

incFastMutInt :: FastMutInt -> IO Int	-- Returns original value
incFastMutInt (FastMutInt arr) = IO $ \s0 ->
  case readIntArray# arr 0# s0 of { (# s1, i #) ->
  case writeIntArray# arr 0# (i +# 1#) s1 of { s ->
  (# s, I# i #) } }

incFastMutIntBy :: FastMutInt -> Int -> IO Int	-- Returns original value
incFastMutIntBy (FastMutInt arr) (I# n) = IO $ \s0 ->
  case readIntArray# arr 0# s0 of { (# s1, i #) ->
  case writeIntArray# arr 0# (i +# n) s1 of { s ->
  (# s, I# i #) } }


