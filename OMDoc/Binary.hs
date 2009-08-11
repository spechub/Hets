{- |
Module      :  $Header$
Description :  Additional (manual) Binary instances for OMDoc
Copyright   :  (c) DFKI GmbH 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(overlapping Typeable instances)
-}

module OMDoc.Binary where

import Network.URI
import Common.BinaryInstances

instance Binary URI where
  put xv = case xv of
    URI a b c d e -> do
      put a
      put b
      put c
      put d
      put e
  get = do
      a <- get
      b <- get
      c <- get
      d <- get
      e <- get
      return $ URI a b c d e

instance Binary URIAuth where
  put xv = case xv of
    URIAuth a b c -> do
      put a
      put b
      put c
  get = do
      a <- get
      b <- get
      c <- get
      return $ URIAuth a b c
