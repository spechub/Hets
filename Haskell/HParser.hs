-- needs -package haskell-src
{- HetCATS/Haskell/HParser.hs
   $Id$
   Authors: C. Maeder
   Year:    2003

   Wrapper for Haskell parsing
   Parses Haskell declarations (not a whole module), for use
     in heterogeneous specifications

   toDo: maybe change Language.Haskell.Parser 
   and export the parser for HsDecl

   positions in successfully parsed abstract syntax are wrong
   (they start with 3)
-}

module Haskell.HParser where

import Haskell.Wrapper
import Haskell.Language.Syntax
import Haskell.Language.Pretty
import Haskell.Language.Parser
import Common.Lib.Parsec
import Common.PrettyPrint
import Common.Lib.Pretty

instance PrettyPrint HsDecls where
    printText0 _ hsDecls = 
	vcat (map (text . ((++) "\n") . prettyPrint) hsDecls)

type HsDecls = [HsDecl]

hParser :: GenParser Char st HsDecls
hParser = do p <- getPosition 
	     s <- hStuff
	     let r = parseModuleWithMode (ParseMode $ sourceName p) 
		     ("\nmodule Anonymous where\n" ++ s)
             case r of
		           ParseOk (HsModule _ _ _ _ hsDecls) ->
			       return hsDecls
			   ParseFailed loc msg -> do
			       let q = setSourceColumn (setSourceLine p 
				       (srcLine loc + sourceLine p - 3))
				        $ srcColumn loc
			       setPosition q
			       consumeNothing -- throw "(un)expect..." away
			       fail msg
