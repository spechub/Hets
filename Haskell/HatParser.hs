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
import Haskell.Hatchet.HsParser as HatParser
import Haskell.Hatchet.HsPretty as HatPretty
import Haskell.Hatchet.HsParseMonad
import Common.Lib.Parsec
import Common.PrettyPrint
import Common.Lib.Pretty
-- import Debug.Trace

instance PrettyPrint HsDecls where
     printText0 _ hsDecls = 
         vcat (map (text . ((++) "\n") . HatPretty.render . ppHsDecl) hsDecls)

type HsDecls = [HsDecl]

hatParser :: GenParser Char st HsDecls
hatParser = do p <- getPosition 
               s <- hStuff
--               trace ("@"++s++"@") (return ())
	       let (l, c) = (sourceLine p, sourceColumn p)
                   r = HatParser.parse 
		       ("\nmodule Anonymous where\n" ++ s) 
                          (SrcLoc l 0) c []
               case r of
		           Ok _ (HsModule _ _ _ hsDecls) -> 
--			       trace (showPretty hsDecls " OK!") $ 
				     return hsDecls
			   Failed msg -> do -- no failure position!
			       fail msg
