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
import Text.ParserCombinators.Parsec
import Common.PrettyPrint
import Common.Lib.Pretty
import Common.Result
-- import Debug.Trace

instance PrettyPrint HsDecls where
     printText0 _ ds = 
         vcat (map (text . ((++) "\n") . HatPretty.pp) $ hsDecls ds)


data HsDecls = HsDecls { hsDecls :: [HsDecl] } deriving (Show, Eq)

hatParser :: GenParser Char st HsDecls
hatParser = do p <- getPosition 
               s <- hStuff
	       let (l, c) = (sourceLine p, sourceColumn p)
                   ts = pLexerPass0 lexerflags0 
                        (replicate (l-1) '\n' ++
                         replicate (c-1) ' ' ++ s)
               case parseTokens (HsParser.parse) "" ts of
		           Result _ (Just (HsModule _ _ _ _ ds)) -> 
				     return $ HsDecls ds
			   Result ds Nothing -> unexpected 
                               ('\n' : unlines (map diagString ds)
                                 ++ "(in Haskell code after " ++ shows p ")")
                                                       
 
