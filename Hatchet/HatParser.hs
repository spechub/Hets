{-| 
Module      :  $Header$
Copyright   :  (c) Sonja Groening, Christian Maeder, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

Wrapper for Haskell parsing.
   Parses Haskell declarations (not a whole module), for use
     in heterogeneous specifications
-}

module Hatchet.HatParser where

import Haskell.Wrapper
import Haskell.Hatchet.HsSyn
import Haskell.Hatchet.HsParser as HatParser
import Haskell.Hatchet.HsPretty as HatPretty
import Haskell.Hatchet.HsParseMonad
import Text.ParserCombinators.Parsec
import Common.PrettyPrint
import Common.Lib.Pretty

instance PrettyPrint HsDecls where
     printText0 _ (HsDecls hsDecls) = 
         vcat (map (text . ((++) "\n") . HatPretty.render . ppHsDecl) hsDecls)

data HsDecls = HsDecls [HsDecl] deriving (Eq, Show)

hatParser :: GenParser Char st HsDecls
hatParser = do p <- getPosition 
               s <- hStuff
               let (l, c) = (sourceLine p, sourceColumn p)
                   r = HatParser.parse s 
                          (SrcLoc l 0) c []
               case r of
                           Ok _ (HsModule _ _ _ hsDecls) -> 
                                     return (HsDecls hsDecls)
                           Failed msg -> unexpected msg
