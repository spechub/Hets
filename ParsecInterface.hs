{- HetCATS/Logic.hs
   $Id$
   Till Mossakowski

   Interface for Parsec parsers.
   Generates a ParseFun as needed by Logic.hs
-}

module ParsecInterface
where

import Logic
import Parsec
import ParsecError

-- for a Parsec parser and an initial state, obtain a ParseFun as needed in Logic.hs

toParseFun :: GenParser Char st a -> st -> ParseFun a  
toParseFun p init file line col s = 
   case runParser (do pos <- getPosition
                      let pos' = setSourceColumn (setSourceLine pos line) col
                      setPosition pos'
                      x <- p 
                      s1 <- getInput
                      pos'' <- getPosition
                      return (x,s1,sourceLine pos'',sourceColumn pos'')) 
           init file s of
     Left err -> error (show err)
     Right x -> x