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
{-
   toDo: 

   positions in successfully parsed abstract syntax are wrong
   (they start with 3)
-}

module Haskell.HatParser where

import Haskell.Wrapper
import Haskell.Hatchet.HsSyn
import Haskell.Hatchet.HsParser
import Haskell.Hatchet.HsParseMonad
import Common.Lib.Parsec
import Debug.Trace
-- import Common.PrettyPrint
-- import Common.Lib.Pretty

-- instance PrettyPrint HsDecls where
--     printText0 _ hsDecls = 
--         vcat (map (text . ((++) "\n") . prettyPrint) hsDecls)

type HsDecls = [HsDecl]

hatParser :: GenParser Char st HsDecls
hatParser = do p <- getPosition 
	       s <- hStuff
               trace ("@"++s++"@") (return ())
	       let r = Haskell.Hatchet.HsParser.parse 
		       ("\nmodule Anonymous where\n" ++ s) (SrcLoc 1 1) 0 []
               case r of
		           Ok _ (HsModule _ _ _ hsDecls) -> 
			       trace (show hsDecls++"OK!") $ return hsDecls
			   Failed msg -> do
-- 			       let q = setSourceColumn (setSourceLine p 
-- 				       (srcLine loc + sourceLine p - 3))
-- 				        $ srcColumn loc
-- 			       setPosition q
-- 			       consumeNothing -- throw "(un)expect..." away
			       fail msg
