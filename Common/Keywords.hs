
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

module Common.Keywords where

import Prelude (String)

withinS,
  withS,
  viewS,
  versionS,
  unitS,
  typeS,
  toS,
  thenS,
  specS,
  sortS,
  revealS,
  resultS,
  propS,
  localS,
  libraryS,
  lambdaS,
  inS,
  idemS,
  hideS,
  givenS,
  getS,
  generatedS,
  fromS,
  cofreeS,
  freeS,
  fitS,
  forallS,
  existsS,
  endS,
  commS,
  closedS,
  opS,
  predS,
  varS,
  sS,
  axiomS,
  assocS,
  asS,
  archS,
  andS,
  whenS,
  trueS,
  notS,
  ifS,
  falseS,
  elseS,
  defS,
  diamondS,
  boxS,
  lOr,
  lAnd,
  negS,
  equivS,
  implS,
  exEqual,
  equalS,
  defnS,
  mapsTo,
  barS,
  cDot,
  dotS,
  colonS,
  lessS,
  timesS,
  prodS,
  funS,
  quMark,
  exMark :: String

-- ----------------------------------------------
-- casl special strings 
-- ----------------------------------------------

exMark  = "!" -- in "exists!"
quMark  = "?"
funS  = "->"
prodS  = "*"
timesS  = "\215"
lessS  = "<"
colonS  = ":"

-- ----------------------------------------------
-- casl keywords
-- ----------------------------------------------

dotS  = "."
cDot  = "\183"
barS  = "|"
mapsTo  = "|->"
defnS  = "::="

equalS  = "="
exEqual  = "=e="  -- unusual keyword 
implS  = "=>"
equivS  = "<=>"
negS  = "\172"
lAnd  = "/\\"   -- logical and/or
lOr  = "\\/"
boxS = "[]"
diamondS = "<>"

defS  = "def"
elseS  = "else"
falseS  = "false"
ifS  = "if"
notS  = "not"
trueS  = "true"
whenS  = "when"

andS  = "and"
archS  = "arch"
asS  = "as"
assocS  = "assoc"
axiomS  = "axiom"
sS  = "s" 
varS  = "var"
predS  = "pred"
opS  = "op"
closedS  = "closed"
commS  = "comm"
endS  = "end"
existsS  = "exists"
forallS  = "forall"
fitS  = "fit"
freeS  = "free"
cofreeS  = "cofree"
fromS  = "from"
generatedS  = "generated"
getS  = "get"
givenS  = "given" 
hideS  = "hide"
idemS  = "idem"
inS  = "in"
lambdaS  = "lambda"
libraryS  = "library"
localS  = "local"
propS = "prop"
resultS  = "result"
revealS  = "reveal" 
sortS  = "sort"
specS  = "spec"
thenS  = "then"
toS  = "to"
typeS  = "type"
unitS  = "unit"
versionS  = "version"
viewS  = "view"
withS  = "with"
withinS  = "within"
