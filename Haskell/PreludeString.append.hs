{- |
Module      :  $Header$
Description :  the programatica prelude as string
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2004
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

provide the programatica prelude as a string

-}

module Haskell.PreludeString (preludeDecls) where

import Haskell.HatParser

preludeDecls :: [HsDecl]
preludeDecls = let ts = pLexerPass0 True preludeString
   in case parseTokens parse "Haskell/ProgramaticaPrelude.hs" ts of
      Just (HsModule _ _ _ _ ds) -> ds
      _ -> error "preludeDecls"

preludeString :: String
preludeString =
{- append Haskell/ProgramaticaPrelude.hs by
   utils/appendHaskellPreludeString -}
