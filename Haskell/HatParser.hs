-- needs -package haskell-src
{- HetCATS/Haskell/HParser.hs
   $Id$
   Authors: C. Maeder, S. Groening
   Year:    2003

   Wrapper for Haskell parsing
   Parses Haskell declarations (not a whole module), for use
     in heterogeneous specifications

   toDo: maybe change Language.Haskell.Parser 
   and export the parser for HsDecl

   positions in successfully parsed abstract syntax are wrong
   (they start with 3)
-}

module Haskell.HatParser where

import Haskell.Wrapper
import Haskell.Hatchet.HsSyn
import Haskell.Hatchet.HsParser
import Haskell.Hatchet.HsParseMonad
import Common.Lib.Parsec
-- import Common.PrettyPrint
-- import Common.Lib.Pretty

-- instance PrettyPrint HsDecls where
--     printText0 _ hsDecls = 
--         vcat (map (text . ((++) "\n") . prettyPrint) hsDecls)

type HsDecls = [HsDecl]

hatParser :: GenParser Char st HsDecls
hatParser = do p <- getPosition 
	       s <- hStuff
	       let r = Haskell.Hatchet.HsParser.parse ("\nmodule Anonymous where\n" ++ s) (SrcLoc 1 1) 0 []
               case r of
		           Ok _ (HsModule _ _ _ hsDecls) ->
			       return hsDecls
			   Failed msg -> do
-- 			       let q = setSourceColumn (setSourceLine p 
-- 				       (srcLine loc + sourceLine p - 3))
-- 				        $ srcColumn loc
-- 			       setPosition q
-- 			       consumeNothing -- throw "(un)expect..." away
			       fail msg
