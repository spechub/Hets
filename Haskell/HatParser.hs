{-| 
Module      :  $Header$
Copyright   :  (c) Sonja Groening, Christian Maeder, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable


   Wrapper for Haskell parsing.
   Parses Haskell declarations (not a whole module), for use
     in heterogeneous specifications
-}

module Haskell.HatParser where

import Haskell.Wrapper
import HsModule
import LexerOptions
import PropLexer
import PropParser as HsParser
import PropPosSyntax
import qualified NewPrettyPrint as HatPretty
import ParseMonad
import Common.Lib.Parsec
import Common.PrettyPrint
import Common.Lib.Pretty
-- import Debug.Trace

instance PrettyPrint HsDecls where
     printText0 _ ds = 
         vcat (map (text . ((++) "\n") . HatPretty.pp) $ hsDecls ds)


data HsDecls = HsDecls { hsDecls :: [HsDecl] } deriving (Show, Eq)

hatParser :: GenParser Char st HsDecls
hatParser = do p <- getPosition 
               s <- hStuff
--               trace ("@"++s++"@") (return ())
	       let (l, c) = (sourceLine p, sourceColumn p)
                   ts = pLexerPass0 lexerflags0 s
                   r = parseTokens (HsParser.parse) "" ts 
               case r of
		           Right (HsModule _ _ _ _ ds) -> 
--			       trace (showPretty ds " OK!") $ 
				     return $ HsDecls ds
			   Left msg -> unexpected msg
