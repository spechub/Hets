{-# OPTIONS -fno-warn-missing-signatures #-}
{- HetCATS/CASL/Keywords.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   string constants for CASL keywords to be used for parsing and printing
   all exported identifiers are mixed case (usually keyword plus capital S)

   http://www.cofi.info/Documents/CASL/Summary/
   from 25 March 2001
   C.4 Lexical Syntax
-}

module Keywords where

import Prelude(String)
-- ----------------------------------------------
-- casl special strings 
-- ----------------------------------------------

exMark :: String = "!" -- in "exists!"
quMark :: String = "?"
funS :: String = "->"
prodS :: String = "*"
timesS :: String = "\215"
lessS :: String = "<"
colonS :: String = ":"

-- ----------------------------------------------
-- casl keywords
-- ----------------------------------------------

dotS :: String = "."
cDot :: String = "\183"
barS :: String = "|"
mapsTo :: String = "|->"
defnS :: String = "::="

equalS :: String = "="
exEqual :: String = "=e="  -- unusual keyword 
implS :: String = "=>"
equivS :: String = "<=>"
negS :: String = "\172"
lAnd :: String = "/\\"   -- logical and/or
lOr :: String = "\\/"

defS :: String = "def"
elseS :: String = "else"
falseS :: String = "false"
ifS :: String = "if"
notS :: String = "not"
trueS :: String = "true"
whenS :: String = "when"

andS :: String = "and"
archS :: String = "arch"
asS :: String = "as"
assocS :: String = "assoc"
axiomS :: String = "axiom"
sS :: String = "s" 
varS :: String = "var"
predS :: String = "pred"
opS :: String = "op"
closedS :: String = "closed"
commS :: String = "comm"
endS :: String = "end"
existsS :: String = "exists"
forallS :: String = "forall"
fitS :: String = "fit"
freeS :: String = "free"
fromS :: String = "from"
generatedS :: String = "generated"
getS :: String = "get"
givenS :: String = "given" 
hideS :: String = "hide"
idemS :: String = "idem"
inS :: String = "in"
lambdaS :: String = "lambda"
libraryS :: String = "library"
localS :: String = "local"
resultS :: String = "result"
revealS :: String = "reveal" 
sortS :: String = "sort"
specS :: String = "spec"
thenS :: String = "then"
toS :: String = "to"
typeS :: String = "type"
unitS :: String = "unit"
versionS :: String = "version"
viewS :: String = "view"
withS :: String = "with"
withinS :: String = "within"
