{-# OPTIONS -fno-warn-missing-signatures #-} 
-- ?
{- 
  File:           HetCATS/CSP-CASL/CCKeywords.hs
  Authors:        Daniel Pratsch
  last modified:  4.11.2002
   
  string constants for CSP-CASL w Channels keywords to be used for parsing 
  all exported identifiers are mixed case (usually keyword plus capital S)
-}

module CCKeywords where

import Prelude(String)

-- ----------------------------------------------
-- csp-casl keywords
-- ----------------------------------------------

dataS      :: String = "data"
channelS   :: String = "channel"
processS   :: String = "process"
endS       :: String = "end"
semicolonS :: String = ";"
commaS     :: String = ","
colonS     :: String = ":"
skipS      :: String = "skip"
stopS      :: String = "stop"
ifS        :: String = "if"
thenS      :: String = "then"
oRBracketS :: String = "("
cRBracketS :: String = ")"
oSBracketS :: String = "["
cSBracketS :: String = "]" 
extChoiceS :: String = "[]"
intChoiceS :: String = "|~|"











{- CASL stuff
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
-}