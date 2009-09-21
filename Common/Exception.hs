{-# LANGUAGE CPP #-}
{- |
Module      :  $Header$
Description :  wrapper module for changed exception handling in ghc-6.10.1
Copyright   :  (c) Christian Maeder DFKI Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

for ghc-6.10.1 the import must be changed from Control.Exception to
Control.OldException
-}

module Common.Exception
  ( Exception.catch
  , catchJust
  , try
  , userErrors
  , Exception(..)
  , AsyncException(ThreadKilled)
  ) where

#if __GLASGOW_HASKELL__ < 609
import Control.Exception as Exception
#else
import Control.OldException as Exception
#endif
